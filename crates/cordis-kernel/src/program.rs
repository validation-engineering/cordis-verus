//! A closed, finite component language with actual witnessed interpretation.
//!
//! Code and resource ownership are fixed at construction. A landed stage reads
//! its operands and continuation from that code and the owned entry context;
//! callers cannot supply a different write or continuation after admission.
#[cfg(verus_keep_ghost)]
use crate::episode::binding_set;
#[cfg(verus_keep_ghost)]
use crate::refinement as paper;
use crate::resources::Cell;
use crate::witnessed::{EpisodeError, ResourceEpisode};
use crate::{Binding, Error, Kernel, Phase, Port};
use vstd::prelude::*;

verus! {
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum Instruction {
    Set { index:usize, value:u64, next:usize },
    Copy { source:usize, index:usize, next:usize },
    BranchWrite { test:usize, expected:u64, index:usize, equal_value:u64, unequal_value:u64, equal_next:usize, unequal_next:usize },
}

impl Instruction {
    pub open spec fn valid(&self,pc:usize,length:usize,cells:nat) -> bool {
        match *self {
            Self::Set{index,next,..} => index < cells && pc < next <= length,
            Self::Copy{source,index,next} => source < cells && index < cells && pc < next <= length,
            Self::BranchWrite{test,index,equal_next,unequal_next,..} => test < cells && index < cells
                && pc < equal_next <= length && pc < unequal_next <= length,
        }
    }
    fn check(&self,pc:usize,length:usize,cells:usize) -> (valid:bool)
        ensures valid == self.valid(pc,length,cells as nat),
    {
        match *self {
            Self::Set{index,next,..} => index < cells && pc < next && next <= length,
            Self::Copy{source,index,next} => source < cells && index < cells && pc < next && next <= length,
            Self::BranchWrite{test,index,equal_next,unequal_next,..} => test < cells && index < cells
                && pc < equal_next && equal_next <= length && pc < unequal_next && unequal_next <= length,
        }
    }
    pub open spec fn operands(&self,cells:Seq<Cell>) -> (usize,u64,usize) {
        match *self {
            Self::Set{index,value,next} => (index,value,next),
            Self::Copy{source,index,next} => (index,cells[source as int].value,next),
            Self::BranchWrite{test,expected,index,equal_value,unequal_value,equal_next,unequal_next} =>
                if cells[test as int].value == expected { (index,equal_value,equal_next) }
                else { (index,unequal_value,unequal_next) },
        }
    }
}

pub struct ResultView { pub cells:Seq<Cell>,pub next:usize }

/// A dynamic stage: both its state map and continuation depend on entry values.
pub open spec fn interpret(code:Seq<Instruction>,pc:usize,owner:u64,cells:Seq<Cell>) -> ResultView {
    let (index,value,next) = code[pc as int].operands(cells);
    ResultView {cells:cells.update(index as int,Cell{value,owner:Some(owner),depth:(cells[index as int].depth+1) as u64}),next}
}

/// Evaluate the first `count` real write stages from the fixed entry context.
/// Reaching the terminal continuation leaves this pure prefix unchanged.
pub open spec fn prefix(code:Seq<Instruction>,owner:u64,initial:Seq<Cell>,count:nat) -> ResultView
    decreases count,
{
    if count == 0 { ResultView{cells:initial,next:0} }
    else {
        let previous = prefix(code,owner,initial,(count-1) as nat);
        if previous.next < code.len() { interpret(code,previous.next,owner,previous.cells) }
        else { previous }
    }
}

pub proof fn instruction_bounds(instruction:Instruction,pc:usize,length:usize,cells:Seq<Cell>)
    requires instruction.valid(pc,length,cells.len()),
    ensures instruction.operands(cells).0 < cells.len(), pc < instruction.operands(cells).2 <= length,
{ }

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum ProgramError { InvalidInstruction, NotAdmitted, Effect(EpisodeError) }
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum Outcome { Advanced, Finished }
/// Result of a landing with target drift acknowledged before returning.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum LandOutcome { Advanced, Terminal, Diverted }

/// Counts actual interpreter calls. The final `Finished` call is included in
/// `steps`; a wider counter also covers `usize::MAX` writes plus that call.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub struct RunCount { pub writes: usize, pub steps: u128 }

/// The constructor checks precisely this domain, including both destinations
/// of a data-dependent branch. Every continuation moves strictly forward.
pub open spec fn valid_program(code: Seq<Instruction>, cells: nat) -> bool {
    forall|i: int| 0 <= i < code.len() ==> code[i].valid(i as usize, code.len() as usize, cells)
}

pub struct ProgramEpisode {
    code:Vec<Instruction>,
    owner:u64,
    pc:usize,
    ended:bool,
    episode:ResourceEpisode,
}

impl ProgramEpisode {
    pub closed spec fn code(&self) -> Seq<Instruction> { self.code@ }
    pub closed spec fn owner(&self) -> u64 { self.owner }
    pub closed spec fn position(&self) -> nat { self.pc as nat }
    pub closed spec fn remaining(&self) -> nat { (self.code.len() - self.pc) as nat }
    pub closed spec fn view(&self) -> Seq<Cell> { self.episode.view() }
    pub closed spec fn initial(&self) -> Seq<Cell> { self.episode.initial() }
    pub closed spec fn depth(&self) -> nat { self.episode.depth() }
    pub closed spec fn pending(&self) -> bool { self.episode.pending() }
    pub closed spec fn settled(&self) -> bool { self.episode.settled() }
    pub closed spec fn cancellation(&self) -> bool { self.episode.cancellation() }
    pub closed spec fn ended(&self) -> bool { self.ended }
    pub closed spec fn committed(&self) -> Seq<Binding> { self.episode.committed() }
    pub closed spec fn wf(&self) -> bool {
        &&& self.episode.wf() && self.pc <= self.code.len()
        &&& self.pc == prefix(self.code@,self.owner,self.initial(),self.depth()).next
        &&& self.view() == prefix(self.code@,self.owner,self.initial(),self.depth()).cells
        &&& (self.ended ==> self.pc == self.code.len() && self.settled() && !self.pending())
        &&& (self.depth() > 0 ==> prefix(self.code@,self.owner,self.initial(),(self.depth()-1) as nat).next < self.code.len())
        &&& self.episode.depth() <= self.pc
        &&& self.episode.view().len() == self.episode.initial().len()
        &&& forall|i:int| 0 <= i < self.code.len() ==> self.code[i].valid(i as usize,self.code.len(),self.episode.view().len())
        &&& forall|i:int| 0 <= i < self.episode.initial().len() ==> self.episode.initial()[i].owner.is_none() && self.episode.initial()[i].depth == 0
        &&& forall|i:int| 0 <= i < self.episode.view().len() ==> {
            &&& self.episode.view()[i].owner.is_none() || self.episode.view()[i].owner == Some(self.owner)
            &&& self.episode.view()[i].depth <= self.episode.depth()
            &&& (self.episode.view()[i].depth == 0 ==> self.episode.view()[i] == self.episode.initial()[i])
        }
    }

    /// Reject invalid resource indices and non-forward continuations before any
    /// stage can run. The language is finite without imposing external fuel.
    pub fn new(code:Vec<Instruction>,values:Vec<u64>,owner:u64,committed:Vec<Binding>) -> (out:Result<Self,ProgramError>)
        ensures out.is_ok() == valid_program(code@, values.len() as nat),
            out.is_err() ==> out == Err(ProgramError::InvalidInstruction),
            out.is_ok() ==> out.unwrap().wf() && out.unwrap().code() == code@
            && out.unwrap().owner() == owner && out.unwrap().position() == 0 && out.unwrap().depth() == 0
            && out.unwrap().view() == out.unwrap().initial() && out.unwrap().view().len() == values.len() && !out.unwrap().pending()
            && !out.unwrap().settled() && !out.unwrap().cancellation()
            && !out.unwrap().ended() && out.unwrap().committed() == committed@
            && forall|i: int| 0 <= i < values.len() ==> out.unwrap().initial()[i]
                == (Cell { value: values[i], owner: None, depth: 0 }),
    {
        let mut i = 0;
        while i < code.len()
            invariant i <= code.len(),forall|j:int| 0 <= j < i ==> code[j].valid(j as usize,code.len(),values.len() as nat),
            decreases code.len()-i,
        {
            if !code[i].check(i,code.len(),values.len()) { return Err(ProgramError::InvalidInstruction); }
            i += 1;
        }
        let episode = ResourceEpisode::new(values,committed);
        Ok(Self {code,owner,pc:0,ended:false,episode})
    }

    pub fn admit(&mut self,target:Option<&[Binding]>) -> (accepted:bool)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).code() == old(self).code(),final(self).owner() == old(self).owner(),
            final(self).view() == old(self).view(),final(self).initial() == old(self).initial(),
            final(self).position() == old(self).position(),final(self).depth() == old(self).depth(),
            final(self).committed() == old(self).committed(),final(self).ended() == old(self).ended(),accepted == final(self).pending(),
            accepted == (old(self).pending() || (!old(self).settled()
                && !old(self).cancellation() && target.is_some()
                && binding_set(target.unwrap()@) == binding_set(old(self).committed()))),
            final(self).settled() == !accepted,
            final(self).cancellation() == (old(self).cancellation()
                || !(target.is_some() && binding_set(target.unwrap()@) == binding_set(old(self).committed()))),
    { self.episode.admit(target) }

    /// Land the admitted instruction selected by private code and pc. Branches
    /// read the entry context before writing. Successful stages strictly lower
    /// remaining code rank; the final admitted empty continuation settles.
    pub fn step(&mut self) -> (result:Result<Outcome,ProgramError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).code() == old(self).code(),final(self).owner() == old(self).owner(),
            final(self).initial() == old(self).initial(),final(self).committed() == old(self).committed(),
            final(self).cancellation() == old(self).cancellation(),
            result.is_ok() == old(self).pending(),
            result == Ok(Outcome::Advanced) ==> {
                let expected = interpret(old(self).code(),old(self).position() as usize,old(self).owner(),old(self).view());
                &&& final(self).view() == expected.cells && final(self).position() == expected.next
                &&& final(self).depth() == old(self).depth()+1 && !final(self).pending() && !final(self).ended()
                &&& final(self).settled() == old(self).cancellation()
                &&& final(self).remaining() < old(self).remaining()
            },
            result == Ok(Outcome::Finished) ==> old(self).position() == old(self).code().len()
                && final(self).position() == old(self).position() && final(self).view() == old(self).view()
                && final(self).depth() == old(self).depth() && final(self).settled() && !final(self).pending() && final(self).ended(),
            result.is_err() ==> *final(self) == *old(self),
            result.is_err() ==> final(self).position() == old(self).position() && final(self).view() == old(self).view()
                && final(self).depth() == old(self).depth() && final(self).pending() == old(self).pending(),
    {
        if !self.episode.is_pending() { return Err(ProgramError::NotAdmitted); }
        if self.pc == self.code.len() {
            let _accepted = self.episode.end();
            assert(_accepted);
            self.ended = true;
            return Ok(Outcome::Finished);
        }
        let ghost prior = *self;
        let instruction = self.code[self.pc];
        let (index,value,next) = match instruction {
            Instruction::Set{index,value,next} => (index,value,next),
            Instruction::Copy{source,index,next} => (index,self.episode.read(source).unwrap(),next),
            Instruction::BranchWrite{test,expected,index,equal_value,unequal_value,equal_next,unequal_next} => {
                if self.episode.read(test).unwrap() == expected { (index,equal_value,equal_next) }
                else { (index,unequal_value,unequal_next) }
            },
        };
        proof { instruction_bounds(instruction,self.pc,self.code.len(),self.view()); }
        assert((index,value,next) == instruction.operands(self.view()));
        assert(self.episode.view()[index as int].depth < u64::MAX);
        let _written = self.episode.land_write(self.owner,index,value);
        assert(_written.is_ok());
        self.pc = next;
        proof {
            assert forall|i:int| 0 <= i < self.episode.view().len() implies {
                &&& self.episode.view()[i].owner.is_none() || self.episode.view()[i].owner == Some(self.owner)
                &&& self.episode.view()[i].depth <= self.episode.depth()
            &&& (self.episode.view()[i].depth == 0 ==> self.episode.view()[i] == self.episode.initial()[i])
            } by {
                if i != index { assert(self.episode.view()[i] == prior.episode.view()[i]); }
            }
        }
        Ok(Outcome::Advanced)
    }

    /// Run this fixed program with its complete binding set held constant;
    /// target order and repeated bindings do not change provider identity. The actual first
    /// admission rejects a mismatched target or a closed/cancelled episode;
    /// an already pending stage is retained and rejected before admission.
    /// Every subsequent admission and landing follows from the checked domain.
    /// This synchronous client covers neither dynamic children nor arbitrary
    /// host futures, target changes, cancellation, or service publication.
    pub fn run_to_completion(&mut self, target: &[Binding]) -> (result: Result<RunCount, ProgramError>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).code() == old(self).code(),
            final(self).owner() == old(self).owner(), final(self).initial() == old(self).initial(),
            final(self).committed() == old(self).committed(),
            result.is_ok() == (!old(self).pending() && !old(self).settled()
                && !old(self).cancellation() && binding_set(target@) == binding_set(old(self).committed())),
            result.is_ok() ==> !final(self).cancellation() && final(self).ended()
                && final(self).settled() && !final(self).pending()
                && final(self).position() == final(self).code().len()
                && final(self).depth() == old(self).depth() + result.unwrap().writes
                && result.unwrap().writes <= old(self).remaining()
                && result.unwrap().steps == result.unwrap().writes as nat + 1,
            result.is_err() ==> result == Err(ProgramError::NotAdmitted)
                && final(self).view() == old(self).view() && final(self).depth() == old(self).depth()
                && final(self).position() == old(self).position() && final(self).ended() == old(self).ended()
                && final(self).pending() == old(self).pending(),
    {
        if self.is_pending() { return Err(ProgramError::NotAdmitted); }
        if !self.admit(Some(target)) { return Err(ProgramError::NotAdmitted); }
        let mut writes: usize = 0;
        let mut steps: u128 = 0;
        while !self.has_ended()
            invariant self.wf(), !self.cancellation(),
                self.pending() == !self.ended(), self.settled() == self.ended(),
                self.code() == old(self).code(), self.owner() == old(self).owner(),
                self.initial() == old(self).initial(), self.committed() == old(self).committed(),
                binding_set(target@) == binding_set(self.committed()),
                self.depth() == old(self).depth() + writes,
                writes as nat + self.remaining() <= old(self).remaining(),
                steps == writes as nat + if self.ended() { 1nat } else { 0nat },
            decreases self.remaining() + if self.ended() { 0nat } else { 1nat },
        {
            let outcome = self.step();
            assert(outcome.is_ok());
            steps += 1;
            match outcome.unwrap() {
                Outcome::Advanced => {
                    writes += 1;
                    let _admitted = self.admit(Some(target));
                    assert(_admitted);
                },
                Outcome::Finished => {},
            }
        }
        Ok(RunCount { writes, steps })
    }

    /// Construct, execute every real stage through `Finished`, and invoke the
    /// actual inverse journal. Invalid instructions are rejected by `new`;
    /// accepted programs return their original cells and an exact call count.
    pub fn execute_and_recover(code: Vec<Instruction>, values: Vec<u64>, owner: u64,
        committed: Vec<Binding>, target: &[Binding]) -> (out: Result<(Self, RunCount), ProgramError>)
        ensures out.is_ok() == (valid_program(code@, values.len() as nat) && binding_set(target@) == binding_set(committed@)),
            !valid_program(code@, values.len() as nat) ==> out == Err(ProgramError::InvalidInstruction),
            valid_program(code@, values.len() as nat) && binding_set(target@) != binding_set(committed@) ==> out == Err(ProgramError::NotAdmitted),
            out.is_ok() ==> {
                let recovered = out.unwrap().0;
                let count = out.unwrap().1;
                &&& recovered.wf() && recovered.code() == code@ && recovered.owner() == owner
                &&& recovered.committed() == committed@ && recovered.view() == recovered.initial()
                &&& recovered.view().len() == values.len() && recovered.depth() == 0
                &&& recovered.position() == 0 && recovered.settled() && !recovered.pending() && !recovered.ended()
                &&& count.writes <= code.len() && count.steps == count.writes as nat + 1
                &&& forall|i: int| 0 <= i < values.len() ==> recovered.view()[i]
                    == (Cell { value: values[i], owner: None, depth: 0 })
            },
    {
        let mut program = Self::new(code, values, owner, committed)?;
        let count = program.run_to_completion(target)?;
        let _restored = program.rollback();
        assert(_restored);
        Ok((program, count))
    }

    pub fn cancel(&mut self)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).code() == old(self).code(),final(self).owner() == old(self).owner(),
            final(self).view() == old(self).view(),final(self).initial() == old(self).initial(),
            final(self).position() == old(self).position(),final(self).depth() == old(self).depth(),
            final(self).pending() == old(self).pending(),final(self).settled() == !old(self).pending(),
            final(self).cancellation(),
            final(self).ended() == old(self).ended(),
            final(self).committed() == old(self).committed(),
    { self.episode.cancel(); }

    /// Consume actual yielded inverses in reverse order. A pending stage is
    /// retained; the interpreter never invents an inverse for an unlanded write.
    pub fn rollback(&mut self) -> (completed:bool)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).code() == old(self).code(),final(self).owner() == old(self).owner(),
            final(self).initial() == old(self).initial(),final(self).committed() == old(self).committed(),
            completed == old(self).settled(),
            completed ==> final(self).position() == 0 && final(self).depth() == 0 && final(self).view() == old(self).initial() && !final(self).ended(),
            !completed ==> final(self).position() == old(self).position() && final(self).depth() == old(self).depth()
                && final(self).view() == old(self).view(),
            final(self).pending() == old(self).pending(),final(self).settled() == old(self).settled(),
    {
        let completed = self.episode.rollback();
        if completed { self.pc = 0; self.ended = false; }
        completed
    }

    pub fn restart(&mut self,committed:Vec<Binding>) -> (accepted:bool)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).code() == old(self).code(),final(self).owner() == old(self).owner(),
            final(self).view() == old(self).view(),final(self).initial() == old(self).initial(),
            final(self).depth() == old(self).depth(),
            accepted == (old(self).depth() == 0 && !old(self).pending()),
            accepted ==> final(self).position() == 0 && !final(self).pending() && !final(self).settled() && !final(self).ended()
                && !final(self).cancellation() && final(self).committed() == committed@,
            !accepted ==> final(self).committed() == old(self).committed()
                && final(self).pending() == old(self).pending() && final(self).settled() == old(self).settled()
                && final(self).cancellation() == old(self).cancellation(),
            !accepted ==> final(self).position() == old(self).position(),
    {
        let accepted = self.episode.restart(committed);
        if accepted { self.pc = 0; self.ended = false; }
        accepted
    }

    /// Publication is checked against actual cells, including branches that
    /// skipped code. Merely reaching the final instruction is insufficient.
    pub fn all_written(&self) -> (complete:bool)
        ensures complete == (forall|i:int| 0 <= i < self.view().len() ==> self.view()[i].depth > 0),
    {
        let length = self.episode.resource_len();
        let mut i = 0;
        while i < length
            invariant i <= length,length == self.view().len(),
                forall|j:int| 0 <= j < i ==> self.view()[j].depth > 0,
            decreases length-i,
        {
            if !self.episode.written(i) { return false; }
            i += 1;
        }
        true
    }

    pub fn read(&self,index:usize) -> (value:Option<u64>)
        ensures value == if index < self.view().len() {Some(self.view()[index as int].value)} else {None},
    { self.episode.read(index) }

    pub proof fn complete_recovery(&self)
        requires self.wf(),self.depth() == 0,
        ensures self.view() == self.initial(),
    { self.episode.complete_recovery(); }

    pub fn code_len(&self) -> (length:usize) ensures length == self.code().len(), { self.code.len() }
    pub fn position_now(&self) -> (pc:usize) ensures pc == self.position(), { self.pc }
    pub fn remaining_now(&self) -> (rank:usize)
        requires self.wf(),ensures rank == self.remaining(),
    { self.code.len()-self.pc }
    pub fn has_ended(&self) -> (ended:bool) ensures ended == self.ended(), { self.ended }
    pub fn is_pending(&self) -> (pending:bool) ensures pending == self.pending(), { self.episode.is_pending() }
    pub fn is_settled(&self) -> (settled:bool) ensures settled == self.settled(), { self.episode.is_settled() }
}


/// The verified interpreter and lifecycle registry share one private owner.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum ProgramDriverError { Kernel(Error), Program(ProgramError), Pending, InvalidLayout, IncompleteProvision }

pub struct ProgramDriver { kernel: Kernel, episodes: Vec<ProgramEpisode>, layouts:Vec<Vec<Port>> }
impl Default for ProgramDriver {
    fn default() -> Self { Self::new() }
}
impl ProgramDriver {
    pub closed spec fn snapshot(&self) -> crate::program_refinement::Snapshot {
        crate::program_refinement::Snapshot {
            allocated:self.kernel.next_id(),
            control:self.control(),
            layouts:IMap::new(|n:usize| paper::registered(self.control(),n),|n:usize| self.layout(n)),
            codes:IMap::new(|n:usize| paper::registered(self.control(),n),|n:usize| self.program(n)),
            initial:IMap::new(|n:usize| paper::registered(self.control(),n),|n:usize| self.initial(n)),
            cells:IMap::new(|n:usize| paper::registered(self.control(),n),|n:usize| self.resource(n)),
            owners:IMap::new(|n:usize| paper::registered(self.control(),n),|n:usize| self.owner(n)),
            positions:IMap::new(|n:usize| paper::registered(self.control(),n),|n:usize| self.position(n)),
            depths:IMap::new(|n:usize| paper::registered(self.control(),n),|n:usize| self.depth(n)),
            ended:IMap::new(|n:usize| paper::registered(self.control(),n),|n:usize| self.ended(n)),
        }
    }
    pub proof fn snapshot_well_formed(&self)
        requires self.wf(),
        ensures crate::program_refinement::wf(self.snapshot()),
    {
        self.kernel.refines_paper();
        let x = self.snapshot();
        assert(x.layouts.dom() =~= x.control.fibers.dom());
        assert(x.codes.dom() =~= x.control.fibers.dom());
        assert(x.initial.dom() =~= x.control.fibers.dom());
        assert(x.cells.dom() =~= x.control.fibers.dom());
        assert(x.owners.dom() =~= x.control.fibers.dom());
        assert(x.positions.dom() =~= x.control.fibers.dom());
        assert(x.depths.dom() =~= x.control.fibers.dom());
        assert(x.ended.dom() =~= x.control.fibers.dom());
        assert forall|n:usize| paper::registered(x.control,n) implies n < x.allocated by { self.kernel.paper_observations(n); }
        assert forall|n:usize| paper::registered(self.control(),n) implies crate::program_refinement::row_wf(self.snapshot(),n) by {
            self.kernel.paper_observations(n);
            assert(n < self.episodes.len());
            assert(Self::good(self.control(),&self.episodes[n as int],n,self.layouts[n as int]@));
        }
    }
    proof fn snapshot_frame(&self,prior:&Self,actor:usize)
        requires self.wf(),prior.wf(),self.control().fibers.dom() == prior.control().fibers.dom(),
            self.episodes.len() == prior.episodes.len(),self.layouts@ == prior.layouts@,
            forall|i:int| 0 <= i < self.episodes.len() && i != actor ==> self.episodes[i] == prior.episodes[i],
            actor < self.episodes.len() ==> self.program(actor) == prior.program(actor)
                && self.initial(actor) == prior.initial(actor) && self.owner(actor) == prior.owner(actor),
        ensures crate::program_refinement::row_frame(prior.snapshot(),self.snapshot(),actor),
    {
        assert forall|n:usize| paper::registered(prior.control(),n) implies {
            &&& prior.snapshot().layouts[n] == self.snapshot().layouts[n] && prior.snapshot().codes[n] == self.snapshot().codes[n]
            &&& prior.snapshot().initial[n] == self.snapshot().initial[n] && prior.snapshot().owners[n] == self.snapshot().owners[n]
            &&& (n != actor ==> prior.snapshot().cells[n] == self.snapshot().cells[n] && prior.snapshot().positions[n] == self.snapshot().positions[n]
                && prior.snapshot().depths[n] == self.snapshot().depths[n] && prior.snapshot().ended[n] == self.snapshot().ended[n])
        } by {
            prior.kernel.paper_observations(n);
            assert(n < self.episodes.len());
            if n != actor { assert(self.episodes[n as int] == prior.episodes[n as int]); }
        }
    }
    proof fn passive_frame(&self,prior:&Self)
        requires self.wf(),prior.wf(),
            forall|i:int| 0 <= i < self.episodes.len() && i < prior.episodes.len()
                ==> self.episodes[i] == prior.episodes[i] && self.layouts[i]@ == prior.layouts[i]@,
        ensures forall|n:usize| paper::registered(prior.control(),n) && paper::registered(self.control(),n)
            ==> crate::program_refinement::metadata_equal(prior.snapshot(),self.snapshot(),n),
    {
        assert forall|n:usize| paper::registered(prior.control(),n) && paper::registered(self.control(),n)
            implies crate::program_refinement::metadata_equal(prior.snapshot(),self.snapshot(),n) by {
            self.kernel.paper_observations(n);prior.kernel.paper_observations(n);
            assert(self.episodes[n as int] == prior.episodes[n as int]);
        }
    }
    pub closed spec fn control(&self) -> paper::State { self.kernel.paper() }
    pub closed spec fn resource(&self, id: usize) -> Seq<crate::resources::Cell> { self.episodes[id as int].view() }
    pub closed spec fn layout(&self,id:usize) -> Seq<Port> { self.layouts[id as int]@ }
    pub closed spec fn program(&self,id:usize) -> Seq<Instruction> { self.episodes[id as int].code() }
    pub closed spec fn position(&self,id:usize) -> nat { self.episodes[id as int].position() }
    pub closed spec fn depth(&self,id:usize) -> nat { self.episodes[id as int].depth() }
    pub closed spec fn ended(&self,id:usize) -> bool { self.episodes[id as int].ended() }
    pub closed spec fn owner(&self,id:usize) -> u64 { self.episodes[id as int].owner() }
    pub closed spec fn initial(&self, id: usize) -> Seq<crate::resources::Cell> { self.episodes[id as int].initial() }
    pub closed spec fn pending(&self, id: usize) -> bool { self.episodes[id as int].pending() }
    pub closed spec fn settled(&self, id: usize) -> bool { self.episodes[id as int].settled() }
    pub closed spec fn cancellation(&self, id: usize) -> bool { self.episodes[id as int].cancellation() }
    pub open spec fn good(s: paper::State, e: &ProgramEpisode, id: usize, layout:Seq<Port>) -> bool {
        &&& layout.len() == e.view().len()
        &&& forall|i:int,j:int| 0 <= i < layout.len() && 0 <= j < layout.len() && layout[i] == layout[j] ==> i == j
        &&& (paper::registered(s,id) ==> s.fibers[id].provisions == ISet::new(|p:Port| layout.contains(p)))
        &&& (paper::registered(s,id) && s.fibers[id].phase == Phase::Active
            ==> forall|i:int| 0 <= i < e.view().len() ==> e.view()[i].depth > 0)
        &&& e.wf()
        &&& (!paper::registered(s, id) || s.fibers[id].phase == Phase::Inactive ==> e.depth() == 0 && !e.pending())
        &&& (paper::registered(s, id) && s.fibers[id].phase == Phase::Active ==> e.settled() && e.position() == e.code().len() && e.ended())
        &&& (paper::registered(s, id) && s.fibers[id].phase != Phase::Inactive
            ==> s.fibers[id].committed == ISet::new(|b: crate::Binding| e.committed().contains(b)))
    }
    pub closed spec fn wf(&self) -> bool {
        self.kernel.wf() && self.episodes.len() == self.kernel.next_id() && self.layouts.len() == self.episodes.len()
            && forall|i: int| 0 <= i < self.episodes.len() ==> Self::good(self.control(), &self.episodes[i], i as usize,self.layouts[i]@)
    }
    proof fn framed(&self, prior: &Self, actor: usize)
        requires prior.wf(), self.kernel.wf(), self.episodes.len() == self.kernel.next_id(),self.layouts.len() == self.episodes.len(),
            paper::frame(prior.control(), self.control(), actor),
            forall|i: int| 0 <= i < self.episodes.len() && i != actor ==> i < prior.episodes.len() && self.episodes[i] == prior.episodes[i] && self.layouts[i]@ == prior.layouts[i]@,
            actor < self.episodes.len() ==> Self::good(self.control(), &self.episodes[actor as int], actor,self.layouts[actor as int]@),
        ensures self.wf(),
    {
        assert forall|i: int| 0 <= i < self.episodes.len() implies Self::good(self.control(), &self.episodes[i], i as usize,self.layouts[i]@) by {
            if i != actor {
                assert(i as usize != actor);
                assert(paper::registered(prior.control(), i as usize) == paper::registered(self.control(), i as usize));
                if paper::registered(prior.control(), i as usize) { assert(prior.control().fibers[i as usize] == self.control().fibers[i as usize]); }
            }
        }
    }

    pub fn new() -> (out: Self)
        ensures out.wf(), out.control().fibers.dom().is_empty(),
    { Self { kernel: Kernel::new(), episodes: Vec::new(),layouts:Vec::new() } }

    /// Fix the whole program and context before allocating its fiber.
    pub fn insert(&mut self,parent:Option<usize>,dependencies:Vec<Port>,provisions:Vec<Port>,
        code:Vec<Instruction>,values:Vec<u64>,owner:u64) -> (r:Result<usize,ProgramDriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),r.is_ok() ==> paper::step(old(self).control(),final(self).control(),r.unwrap(),paper::Rule::Insert)
            && crate::program_refinement::passive_ack(old(self).snapshot(),final(self).snapshot(),r.unwrap(),paper::Rule::Insert),
    {
        if values.len() != provisions.len() { return Err(ProgramDriverError::InvalidLayout); }
        let mut layout = Vec::new();
        let mut i = 0;
        while i < provisions.len()
            invariant self.wf(),*self == *old(self),i <= provisions.len(),layout@ == provisions@.subrange(0,i as int),
                forall|j:int,k:int| 0 <= j < i && 0 <= k < i && provisions[j] == provisions[k] ==> j == k,
            decreases provisions.len()-i,
        {
            let mut j = 0;
            while j < i
                invariant self.wf(),*self == *old(self),j <= i,i < provisions.len(),
                    forall|k:int| 0 <= k < j ==> provisions[k] != provisions[i as int],
                decreases i-j,
            {
                if provisions[j] == provisions[i] { return Err(ProgramDriverError::InvalidLayout); }
                j += 1;
            }
            layout.push(provisions[i]);
            i += 1;
            assert(layout@ =~= provisions@.subrange(0,i as int));
        }
        assert(layout@ == provisions@);
        let program = match ProgramEpisode::new(code,values,owner,Vec::new()) {
            Ok(program) => program,
            Err(error) => { return Err(ProgramDriverError::Program(error)); },
        };
        let ghost prior = *self;
        match self.kernel.insert(parent,dependencies,provisions) {
            Err(e) => { proof { self.kernel.unchanged_observations(&prior.kernel); } Err(ProgramDriverError::Kernel(e)) },
            Ok(id) => {
                self.episodes.push(program);
                self.layouts.push(layout);
                proof {
                    assert(self.control().fibers[id].provisions =~= ISet::new(|p:Port| self.layout(id).contains(p)));
                    self.framed(&prior,id); self.passive_frame(&prior);
                }
                Ok(id)
            },
        }
    }

    /// L-Begin changes only control and iterator metadata; resource values are
    /// preserved from the previous complete recovery (or initial insertion).
    pub fn begin(&mut self, id: usize) -> (r: Result<(), ProgramDriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),
            r.is_ok() ==> paper::step(old(self).control(), final(self).control(), id, paper::Rule::Begin)
                && final(self).resource(id) == final(self).initial(id)
                && final(self).resource(id) == old(self).resource(id)
                && !final(self).pending(id) && !final(self).settled(id) && !final(self).cancellation(id)
                && paper::coherent(final(self).control(), id)
                && crate::program_refinement::begin_ack(old(self).snapshot(),final(self).snapshot(),id),
    {
        let ghost prior = *self;
        match self.kernel.begin(id) {
            Err(e) => { proof { self.kernel.unchanged_observations(&prior.kernel); } Err(ProgramDriverError::Kernel(e)) },
            Ok(()) => {
                proof { self.kernel.paper_observations(id); }
                let bindings = self.kernel.committed(id);
                let _restarted = self.episodes[id].restart(bindings);
                assert(_restarted);
                proof { self.kernel.paper_iteration_guard(id); self.episodes[id as int].complete_recovery(); self.framed(&prior, id); crate::program_refinement::domain_preserved(prior.control(),self.control(),id); self.snapshot_frame(&prior,id); }
                Ok(())
            },
        }
    }

    /// New admission observes the live kernel target; outstanding stages remain
    /// admitted across target drift, exactly as the witnessed protocol requires.
    pub fn admit(&mut self, id: usize) -> (r: Result<bool, ProgramDriverError>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).control() == old(self).control(),
            r.is_ok() == (paper::registered(old(self).control(), id)
                && old(self).control().fibers[id].phase == Phase::Loading),
            r.is_err() ==> *final(self) == *old(self),
            r.is_ok() ==> crate::program_refinement::administrative(old(self).snapshot(),final(self).snapshot(),id)
                && r.unwrap() == (old(self).pending(id) || (!old(self).settled(id)
                    && !old(self).cancellation(id) && paper::coherent(old(self).control(), id)))
                && final(self).pending(id) == r.unwrap() && final(self).settled(id) == !r.unwrap()
                && final(self).cancellation(id) == (old(self).cancellation(id)
                    || !paper::coherent(old(self).control(), id)),
    {
        let ghost prior = *self;
        proof { self.kernel.paper_observations(id); }
        if self.kernel.phase(id) != Some(Phase::Loading) { return Err(ProgramDriverError::Kernel(Error::InvalidState)); }
        let target = self.kernel.target(id);
        let result = match target {
            Some(target) => {
                proof { self.kernel.paper_captured_target(id, self.episodes[id as int].committed(), Some(target@)); }
                self.episodes[id].admit(Some(target.as_slice()))
            },
            None => {
                proof { self.kernel.paper_captured_target(id, self.episodes[id as int].committed(), None); }
                self.episodes[id].admit(None)
            },
        };
        proof { self.framed(&prior, id); self.snapshot_frame(&prior,id); }
        Ok(result)
    }

    /// The landing payload is exclusively determined by the installed program.
    pub fn step(&mut self,id:usize) -> (r:Result<Outcome,ProgramDriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).control() == old(self).control(),
            r.is_ok() ==> !final(self).pending(id),
            r == Ok(Outcome::Finished) ==> crate::program_refinement::terminal_poll(old(self).snapshot(),final(self).snapshot(),id),
            r == Ok(Outcome::Advanced) ==> crate::program_refinement::landed(old(self).snapshot(),final(self).snapshot(),id),
            r == Ok(Outcome::Advanced) ==> final(self).resource(id) ==
                interpret(old(self).program(id),old(self).position(id) as usize,old(self).owner(id),old(self).resource(id)).cells
                && final(self).position(id) ==
                    interpret(old(self).program(id),old(self).position(id) as usize,old(self).owner(id),old(self).resource(id)).next,
    {
        let ghost prior = *self;
        proof { self.kernel.paper_observations(id); }
        if self.kernel.phase(id) != Some(Phase::Loading) { return Err(ProgramDriverError::Kernel(Error::InvalidState)); }
        let result = match self.episodes[id].step() {
            Ok(outcome) => Ok(outcome), Err(e) => Err(ProgramDriverError::Program(e)),
        };
        proof { self.framed(&prior,id); self.snapshot_frame(&prior,id); }
        result
    }

    /// Execute the admitted stage and acknowledge a changed target atomically.
    /// A terminal result still needs `finish`, which checks total provision.
    /// `program_trace::local_refinement` connects this concrete acknowledgement
    /// to L-Iter, landing L-Divert, or a terminal administrative stutter.
    #[verifier::rlimit(30)]
    pub fn land(&mut self,id:usize) -> (r:Result<LandOutcome,ProgramDriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),
            r.is_ok() ==> crate::program_trace::atomic_ack(old(self).snapshot(),final(self).snapshot(),id,r.unwrap()),
    {
        let ghost entry=*self;
        let outcome=self.step(id)?;
        let ghost middle=*self;
        proof {
            entry.snapshot_well_formed();self.snapshot_well_formed();
            self.kernel.paper_observations(id);
            assert(paper::registered(self.control(),id));
            assert(self.control().fibers[id].phase == Phase::Loading);
        }
        match self.kernel.leave_if_changed(id) {
            Ok(()) => {
                self.episodes[id].cancel();
                proof {
                    self.framed(&middle,id);
                    crate::program_refinement::domain_preserved(middle.control(),self.control(),id);
                    self.snapshot_frame(&middle,id);self.snapshot_well_formed();
                    assert(crate::program_refinement::depart_ack(middle.snapshot(),self.snapshot(),id));
                    assert(crate::program_trace::atomic_ack(entry.snapshot(),self.snapshot(),id,LandOutcome::Diverted));
                }
                Ok(LandOutcome::Diverted)
            },
            Err(_error) => {
                proof {
                    self.kernel.unchanged_observations(&middle.kernel);
                    self.framed(&middle,id);self.snapshot_frame(&middle,id);self.snapshot_well_formed();
                    assert(_error == Error::Changed);
                    assert(self.snapshot().layouts =~= middle.snapshot().layouts);
                    assert(self.snapshot().codes =~= middle.snapshot().codes);
                    assert(self.snapshot().initial =~= middle.snapshot().initial);
                    assert(self.snapshot().cells =~= middle.snapshot().cells);
                    assert(self.snapshot().owners =~= middle.snapshot().owners);
                    assert(self.snapshot().positions =~= middle.snapshot().positions);
                    assert(self.snapshot().depths =~= middle.snapshot().depths);
                    assert(self.snapshot().ended =~= middle.snapshot().ended);
                    assert(self.snapshot() == middle.snapshot());
                }
                let result=match outcome {Outcome::Advanced=>LandOutcome::Advanced,Outcome::Finished=>LandOutcome::Terminal};
                Ok(result)
            },
        }
    }

    pub fn finish(&mut self, id: usize) -> (r: Result<(), ProgramDriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),
            r.is_ok() ==> paper::step(old(self).control(), final(self).control(), id, paper::Rule::Finish)
                && crate::program_refinement::finish_ack(old(self).snapshot(),final(self).snapshot(),id),
    {
        let ghost prior = *self;
        proof { self.kernel.paper_observations(id); }
        if !self.kernel.contains(id) { return Err(ProgramDriverError::Kernel(Error::Unknown)); }
        if !self.episodes[id].has_ended() || !self.episodes[id].is_settled() || self.episodes[id].position_now() != self.episodes[id].code_len() { return Err(ProgramDriverError::Pending); }
        if !self.episodes[id].all_written() { return Err(ProgramDriverError::IncompleteProvision); }
        match self.kernel.finish(id) {
            Ok(()) => { proof { self.framed(&prior, id); crate::program_refinement::domain_preserved(prior.control(),self.control(),id); self.snapshot_frame(&prior,id); } Ok(()) },
            Err(e) => { proof { self.kernel.unchanged_observations(&prior.kernel); } Err(ProgramDriverError::Kernel(e)) },
        }
    }

    /// Retirement is a control request, preserving pending stages and resources.
    pub fn retire(&mut self, id: usize) -> (r: Result<(), ProgramDriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),
            r.is_ok() ==> paper::step(old(self).control(), final(self).control(), id, paper::Rule::Retire)
                && crate::program_refinement::passive_ack(old(self).snapshot(),final(self).snapshot(),id,paper::Rule::Retire),
    {
        let ghost prior = *self;
        match self.kernel.retire(id) {
            Ok(()) => { proof { self.framed(&prior, id); self.passive_frame(&prior); } Ok(()) },
            Err(e) => { proof { self.kernel.unchanged_observations(&prior.kernel); } Err(ProgramDriverError::Kernel(e)) },
        }
    }

    /// Delay diversion until the admitted stage has landed. The kernel stays
    /// Loading during that interval; it publishes no new provider bindings.
    pub fn depart(&mut self, id: usize) -> (r: Result<(), ProgramDriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),
            r.is_ok() ==> paper::step(old(self).control(), final(self).control(), id,
                if old(self).control().fibers[id].phase == Phase::Loading { paper::Rule::Divert } else { paper::Rule::Leave })
                && crate::program_refinement::depart_ack(old(self).snapshot(),final(self).snapshot(),id),
    {
        let ghost prior = *self;
        proof { self.kernel.paper_observations(id); }
        if !self.kernel.contains(id) { return Err(ProgramDriverError::Kernel(Error::Unknown)); }
        if self.episodes[id].is_pending() { return Err(ProgramDriverError::Pending); }
        match self.kernel.leave_if_changed(id) {
            Err(e) => { proof { self.kernel.unchanged_observations(&prior.kernel); } Err(ProgramDriverError::Kernel(e)) },
            Ok(()) => { self.episodes[id].cancel(); proof { self.framed(&prior, id); crate::program_refinement::domain_preserved(prior.control(),self.control(),id); self.snapshot_frame(&prior,id); } Ok(()) },
        }
    }

    /// Guard, real inverse execution and committed-view release are one verified
    /// method. There is no public access to an unguarded journal rollback.
    pub fn unload(&mut self, id: usize) -> (r: Result<(), ProgramDriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),
            r.is_ok() ==> paper::step(old(self).control(), final(self).control(), id, paper::Rule::Unload)
                && final(self).resource(id) == old(self).initial(id)
                && crate::program_refinement::unload_ack(old(self).snapshot(),final(self).snapshot(),id),
    {
        let ghost prior = *self;
        proof { self.kernel.paper_observations(id); }
        if !self.kernel.contains(id) { return Err(ProgramDriverError::Kernel(Error::Unknown)); }
        if !self.episodes[id].is_settled() || self.episodes[id].is_pending() { return Err(ProgramDriverError::Pending); }
        if self.kernel.phase(id) != Some(Phase::Unloading) { return Err(ProgramDriverError::Kernel(Error::InvalidState)); }
        if let Err(e) = self.kernel.begin_cleanup(id) {
            proof { self.kernel.unchanged_observations(&prior.kernel); }
            return Err(ProgramDriverError::Kernel(e));
        }
        let _restored = self.episodes[id].rollback();
        assert(_restored);
        let ghost middle = self.kernel;
        match self.kernel.finish_cleanup(id) {
            Ok(()) => { proof { self.framed(&prior, id); crate::program_refinement::domain_preserved(prior.control(),self.control(),id); self.snapshot_frame(&prior,id); } Ok(()) },
            Err(e) => { proof { self.kernel.unchanged_observations(&middle); self.framed(&prior, id); crate::program_refinement::domain_preserved(prior.control(),self.control(),id); self.snapshot_frame(&prior,id); } Err(ProgramDriverError::Kernel(e)) },
        }
    }

    pub fn remove(&mut self, id: usize) -> (r: Result<(), ProgramDriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),
            r.is_ok() ==> paper::step(old(self).control(), final(self).control(), id, paper::Rule::Remove)
                && crate::program_refinement::passive_ack(old(self).snapshot(),final(self).snapshot(),id,paper::Rule::Remove),
    {
        let ghost prior = *self;
        match self.kernel.remove(id) {
            Ok(()) => { proof { self.framed(&prior, id); self.passive_frame(&prior); } Ok(()) },
            Err(e) => { proof { self.kernel.unchanged_observations(&prior.kernel); } Err(ProgramDriverError::Kernel(e)) },
        }
    }

    pub fn phase(&self, id: usize) -> (phase: Option<Phase>)
        ensures phase == if paper::registered(self.control(), id) { Some(self.control().fibers[id].phase) } else {None},
    { proof { self.kernel.paper_observations(id); } self.kernel.phase(id) }

    pub fn read(&self, id: usize, index: usize) -> (value: Option<u64>)
        requires self.wf(),
        ensures paper::registered(self.control(), id) && index < self.resource(id).len() ==> value == Some(self.resource(id)[index as int].value),
    {
        proof { self.kernel.paper_observations(id); }
        if !self.kernel.contains(id) { return None; }
        self.episodes[id].read(index)
    }
}

} // verus!
