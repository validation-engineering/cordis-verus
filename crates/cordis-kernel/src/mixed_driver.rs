//! A synchronous interpreter with shared provider tables and one mixed journal.
//!
//! Code is installed before execution. Instructions resolve dependency payloads
//! through the episode's committed provider identity. Child instructions name
//! the expected fresh allocation explicitly; a different allocator result is a
//! strict failure. Transactions execute on a private copy and publish only on
//! success, including complete reverse-order restoration. Copying costs are
//! proportional to the stored machine, including tombstones and installed code.
//!
//! This is a closed synchronous profile with complete tables at publication.
//! A Child instruction carries a fixed expected ID: a second activation or an
//! intervening insertion can therefore fail strictly with UnexpectedChild.
//! There is no asynchronous in-flight landing or arbitrary host callback here.
//! The executable run_script constructs its source execution from the empty
//! configuration; each actual heterogeneous receipt is matched to that history.
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_grammar as d, grammar_lift as lift, mediated as m, mixed_grammar as mx,
    mixed_syntax as syntax, projection, refinement as r, semantics as s,
};
use crate::{Error, Kernel, Phase, Port};
use vstd::prelude::*;

verus! {

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum Instruction {
    Unit,
    Provide { key:Port, value:u64, next:Option<usize> },
    Xor { key:Port, mask:u64, next:Option<usize> },
    Child { expected:usize, blueprint:usize, next:Option<usize> },
}
impl Instruction {
    pub open spec fn continuation(&self)->Option<usize> {
        match *self {Self::Unit=>None,Self::Provide {next,..}=>next,Self::Xor {next,..}=>next,Self::Child {next,..}=>next}
    }
    pub open spec fn valid(&self,pc:usize,length:usize,rank:usize,dependencies:Seq<Port>,provisions:Seq<Port>)->bool {
        (self.continuation().is_some() ==> pc<self.continuation().unwrap()<=length)
        && match *self {
            Self::Unit=>true,
            Self::Provide {key,..}=>provisions.contains(key),
            Self::Xor {key,..}=>dependencies.contains(key) || provisions.contains(key),
            Self::Child {blueprint,..}=>blueprint<rank,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum Inverse {
    Unit,
    Provision { key:Port },
    Xor { provider:usize, key:Port, mask:u64 },
    Child { child:usize },
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub struct Receipt { pub actor:usize, pub inverse:Inverse }

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum DriverError {
    Kernel(Error), InvalidBlueprint, InvalidInstruction, Unknown,
    MissingBinding, MissingValue, AlreadyProvided, UnexpectedChild,
    IncompleteProvision, Retained, NonemptyTable,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum Outcome { Advanced, Finished, Child { child:usize, finished:bool } }

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum Command {
    Insert {parent:Option<usize>,blueprint:usize}, Begin {actor:usize}, Step {actor:usize},
    Retire {actor:usize}, Depart {actor:usize}, Unload {actor:usize}, Remove {actor:usize},
}
/// The two successful outcomes of a departure command.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum Departure { Divert, Leave }

/// A successful checked command. Only a Step carries its actual outcome, and
/// only a Depart carries its routing decision. The command's actor is stored
/// once; insertion additionally records the newly allocated actor.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum Transition {
    Insert { parent:Option<usize>, blueprint:usize, actor:usize },
    Begin { actor:usize },
    Step { actor:usize, outcome:Outcome },
    Retire { actor:usize },
    Depart { actor:usize, departure:Departure },
    Unload { actor:usize },
    Remove { actor:usize },
}
impl Transition {
    pub open spec fn command_spec(&self)->Command {
        match *self {
            Self::Insert {parent,blueprint,..}=>Command::Insert {parent,blueprint},
            Self::Begin {actor}=>Command::Begin {actor},
            Self::Step {actor,..}=>Command::Step {actor},
            Self::Retire {actor}=>Command::Retire {actor},
            Self::Depart {actor,..}=>Command::Depart {actor},
            Self::Unload {actor}=>Command::Unload {actor},
            Self::Remove {actor}=>Command::Remove {actor},
        }
    }
    #[verifier::when_used_as_spec(command_spec)]
    pub fn command(&self)->(out:Command)
        ensures out==self.command_spec(),
    {
        match *self {
            Self::Insert {parent,blueprint,..}=>Command::Insert {parent,blueprint},
            Self::Begin {actor}=>Command::Begin {actor},
            Self::Step {actor,..}=>Command::Step {actor},
            Self::Retire {actor}=>Command::Retire {actor},
            Self::Depart {actor,..}=>Command::Depart {actor},
            Self::Unload {actor}=>Command::Unload {actor},
            Self::Remove {actor}=>Command::Remove {actor},
        }
    }
    pub open spec fn actor_spec(&self)->usize {
        match *self {
            Self::Insert {actor,..}|Self::Begin {actor}|Self::Step {actor,..}|Self::Retire {actor}|
            Self::Depart {actor,..}|Self::Unload {actor}|Self::Remove {actor}=>actor,
        }
    }
    #[verifier::when_used_as_spec(actor_spec)]
    pub fn actor(&self)->(out:usize)
        ensures out==self.actor_spec(),
    {
        match *self {
            Self::Insert {actor,..}|Self::Begin {actor}|Self::Step {actor,..}|Self::Retire {actor}|
            Self::Depart {actor,..}|Self::Unload {actor}|Self::Remove {actor}=>actor,
        }
    }
    pub open spec fn label(&self)->(usize,r::Rule) {
        (self.actor_spec(),match *self {
            Self::Insert {..}=>r::Rule::Insert,Self::Begin {..}=>r::Rule::Begin,
            Self::Step {outcome,..}=>outcome_rule(outcome),Self::Retire {..}=>r::Rule::Retire,
            Self::Depart {departure:Departure::Divert,..}=>r::Rule::Divert,
            Self::Depart {departure:Departure::Leave,..}=>r::Rule::Leave,
            Self::Unload {..}=>r::Rule::Unload,Self::Remove {..}=>r::Rule::Remove,
        })
    }
}
pub open spec fn labels(transitions:Seq<Transition>)->Seq<(usize,r::Rule)> {transitions.map(|_:int,t:Transition|t.label())}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub struct Index { pub blueprint:usize, pub pc:usize }

pub struct Blueprint {
    dependencies:Vec<Port>, provisions:Vec<Port>, code:Vec<Instruction>,
}

impl Blueprint {
    pub closed spec fn dependencies(&self)->Seq<Port> {self.dependencies@}
    pub closed spec fn provisions(&self)->Seq<Port> {self.provisions@}
    pub closed spec fn code(&self)->Seq<Instruction> {self.code@}
    pub closed spec fn same(&self,other:&Self)->bool {
        self.dependencies@==other.dependencies@ && self.provisions@==other.provisions@ && self.code@==other.code@
    }
    pub closed spec fn valid(&self,rank:usize)->bool {
        forall|pc:int| #![trigger self.code[pc]]
            0<=pc<self.code.len() ==> self.code[pc].valid(pc as usize,self.code.len(),rank,self.dependencies@,self.provisions@)
    }
    pub fn new(dependencies:Vec<Port>,provisions:Vec<Port>,code:Vec<Instruction>)->(out:Self)
        ensures out.dependencies()==dependencies@,out.provisions()==provisions@,out.code()==code@,
    {Self {dependencies,provisions,code}}

    fn validate(&self,rank:usize)->(valid:bool)
        ensures valid==self.valid(rank),
    {
        let mut pc=0;
        while pc<self.code.len()
            invariant pc<=self.code.len(),forall|i:int| 0<=i<pc ==> self.code[i].valid(i as usize,self.code.len(),rank,self.dependencies@,self.provisions@),
            decreases self.code.len()-pc,
        {
            let instruction=self.code[pc];
            let next=match instruction {Instruction::Unit=>None,Instruction::Provide {next,..}=>next,
                Instruction::Xor {next,..}=>next,Instruction::Child {next,..}=>next};
            if let Some(next)=next {if next<=pc || next>self.code.len() {return false;}}
            match instruction {
                Instruction::Unit=>{},
                Instruction::Provide {key,..}=>{if !has_port(&self.provisions,key) {return false;}},
                Instruction::Xor {key,..}=>{if !has_port(&self.dependencies,key) && !has_port(&self.provisions,key) {return false;}},
                Instruction::Child {blueprint,..}=>{if blueprint>=rank {return false;}},
            }
            pc+=1;
        }
        true
    }

    fn duplicate(&self)->(out:Self)
        ensures out.same(self),
    {Self {dependencies:copy_vec(&self.dependencies),provisions:copy_vec(&self.provisions),code:copy_vec(&self.code)}}
}

fn has_port(ports:&[Port],key:Port)->(yes:bool)
    ensures yes==ports@.contains(key),
{
    let mut i=0;
    while i<ports.len()
        invariant i<=ports.len(),forall|j:int| 0<=j<i ==> ports[j]!=key,
        decreases ports.len()-i,
    {if ports[i]==key {return true;}i+=1;}
    false
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub struct Slot { pub key:Port, pub value:Option<u64> }

pub struct Table { slots:Vec<Slot> }
impl Table {
    pub closed spec fn view(&self)->Seq<Slot> {self.slots@}
    pub closed spec fn unique(&self)->bool {
        forall|i:int,j:int| 0<=i<self.slots.len() && 0<=j<self.slots.len()
            && self.slots[i].key==self.slots[j].key ==> i==j
    }
    pub closed spec fn find(&self,key:Port)->Option<usize> {
        if exists|i:int| 0<=i<self.slots.len() && self.slots[i].key==key {
            Some((choose|i:int| 0<=i<self.slots.len() && self.slots[i].key==key) as usize)
        } else {None}
    }
    pub closed spec fn map(&self)->IMap<Port,u64> {
        IMap::new(|key:Port|self.find(key).is_some() && self.slots[self.find(key).unwrap() as int].value.is_some(),
            |key:Port|self.slots[self.find(key).unwrap() as int].value.unwrap())
    }
    fn locate(&self,key:Port)->(out:Option<usize>)
        requires self.unique(),
        ensures out==self.find(key),out.is_some() ==> out.unwrap()<self.slots.len() && self.slots[out.unwrap() as int].key==key,
    {
        let mut i=0;
        while i<self.slots.len()
            invariant self.unique(),i<=self.slots.len(),forall|j:int| 0<=j<i ==> self.slots[j].key!=key,
            decreases self.slots.len()-i,
        {
            if self.slots[i].key==key {
                assert(self.find(key).is_some());
                let ghost chosen=self.find(key).unwrap();
                assert(chosen<self.slots.len() && self.slots[chosen as int].key==key);
                assert(self.slots[i as int].key==self.slots[chosen as int].key);
                assert(chosen==i);
                return Some(i);
            }
            i+=1;
        }
        None
    }
    pub fn read(&self,key:Port)->(out:Option<u64>)
        requires self.unique(),
        ensures out==if self.map().dom().contains(key) {Some(self.map()[key])} else {None},
    {match self.locate(key) {None=>None,Some(i)=>self.slots[i].value}}

    fn put(&mut self,index:usize,value:Option<u64>)
        requires old(self).unique(),index<old(self).slots.len(),
        ensures final(self).unique(),final(self).slots.len()==old(self).slots.len(),
            final(self).view()==old(self).view().update(index as int,Slot {key:old(self).view()[index as int].key,value}),
            final(self).map()==match value {Some(v)=>old(self).map().insert(old(self).view()[index as int].key,v),
                None=>old(self).map().remove(old(self).view()[index as int].key)},
    {
        let ghost prior=*self;let key=self.slots[index].key;
        self.slots.set(index,Slot {key,value});
        assert forall|k:Port| self.find(k)==prior.find(k) by {
            if self.find(k).is_some() {let i=self.find(k).unwrap();assert(self.slots[i as int].key==prior.slots[i as int].key);}
            if prior.find(k).is_some() {let i=prior.find(k).unwrap();assert(self.slots[i as int].key==prior.slots[i as int].key);}
        }
        assert(self.map() =~= match value {Some(v)=>prior.map().insert(key,v),None=>prior.map().remove(key)});
    }

    fn duplicate(&self)->(out:Self) ensures out.view()==self.view(),
    {Self {slots:copy_vec(&self.slots)}}

    proof fn same_map(&self,other:&Self)
        requires self.unique(),other.unique(),self.view()==other.view(),
        ensures self.map()==other.map(),
    {
        assert forall|key:Port| self.find(key)==other.find(key) by {
            if self.find(key).is_some() {
                let i=self.find(key).unwrap();assert(other.slots[i as int].key==key);
                assert(other.find(key).is_some());let j=other.find(key).unwrap();
                assert(self.slots[j as int].key==key);assert(i==j);
            } else if other.find(key).is_some() {
                let j=other.find(key).unwrap();assert(self.slots[j as int].key==key);
                assert(self.find(key).is_some());
            }
        }
        assert(self.map() =~= other.map());
    }
}

fn copy_vec<T:Copy>(source:&[T])->(out:Vec<T>)
    ensures out@==source@,
{
    let mut out=Vec::new();let mut i=0;
    while i<source.len()
        invariant i<=source.len(),out@==source@.subrange(0,i as int),
        decreases source.len()-i,
    {out.push(source[i]);i+=1;assert(out@ =~= source@.subrange(0,i as int));}
    assert(out@ =~= source@);out
}

fn copy_kernel(source:&Kernel)->(out:Kernel)
    ensures out.unchanged(source),out.wf()==source.wf(),out.paper()==source.paper(),out.next_id()==source.next_id(),
{
    let out=Kernel {nodes:copy_vec(&source.nodes),declarations:copy_vec(&source.declarations),links:copy_vec(&source.links)};
    proof {out.unchanged_observations(source);}
    out
}

pub open spec fn xor_operation(mask:u64)->m::Operation<u64,()> {
    |value:u64|Some(m::ValueYield {value:value^mask,outcome:(),undo:|current:u64|Some(current^mask)})
}
pub open spec fn library()->d::Library<Port,Port,u64,u64,()> {
    d::Library {values:|_:Port,_:u64|true,arguments:|_:Port,_:u64|true,outcomes:|_:Port,_:()|true,
        key:|key:Port|key,allowed:ISet::full(),apply:|_:Port,mask:u64|xor_operation(mask)}
}
pub proof fn xor_inverse(value:u64,mask:u64)
    ensures (value^mask)^mask==value,
{assert((value^mask)^mask==value) by(bit_vector);}

#[verifier::spinoff_prover]
pub proof fn library_theory()
    ensures d::primitive_theory(|_:Port,a:u64,b:u64|a==b,library()),
{
    reveal(d::primitive_theory);
    let eq=|_:Port,a:u64,b:u64|a==b;
    assert forall|key:Port| #[trigger] m::key_equivalence(eq,key) by { }
    assert forall|key:Port,mask:u64| library().allowed.contains(key) && (library().arguments)(key,mask)
        implies d::operation_typed(library(),key,mask)
            && m::operation_admissible(|a:u64,b:u64|a==b,(library().apply)(key,mask)) by {
        assert forall|value:u64| xor_operation(mask)(value).is_some()
            implies (xor_operation(mask)(value).unwrap().undo)(xor_operation(mask)(value).unwrap().value)==Some(value) by {
            xor_inverse(value,mask);
        }
    }
}

impl Receipt {
    pub open spec fn model(&self)->mx::Receipt<u64> {
        match self.inverse {
            Inverse::Child {child}=>mx::Receipt::Child {actor:self.actor,child},
            Inverse::Unit=>mx::Receipt::Table {receipt:lift::Receipt {actor:self.actor,inverse:lift::Inverse::Unit}},
            Inverse::Provision {key}=>mx::Receipt::Table {receipt:lift::Receipt {actor:self.actor,inverse:lift::Inverse::Provision {key}}},
            Inverse::Xor {provider,key,mask}=>mx::Receipt::Table {receipt:lift::Receipt {actor:self.actor,
                inverse:lift::Inverse::Operation {provider,key,undo:|value:u64|Some(value^mask)}}},
        }
    }
}

pub open spec fn ports(xs:Seq<Port>)->ISet<Port> {ISet::new(|key:Port|xs.contains(key))}
pub open spec fn ports_bindings(xs:Seq<crate::Binding>)->ISet<crate::Binding> {ISet::new(|binding:crate::Binding|xs.contains(binding))}
pub open spec fn continuation(blueprint:usize,next:Option<usize>)->Option<Index> {
    match next {None=>None,Some(pc)=>Some(Index {blueprint,pc})}
}
pub open spec fn instruction_node(bank:Seq<Blueprint>,blueprint:usize,instruction:Instruction)->mx::Node<Port,u64,u64,(),Index> {
    match instruction {
        Instruction::Unit=>mx::Node::Dependent {node:d::Node::Unit},
        Instruction::Provide {key,value,next}=>mx::Node::Dependent {node:d::Node::Provision {key,value,next:continuation(blueprint,next)}},
        Instruction::Xor {key,mask,next}=>mx::Node::Dependent {node:d::Node::Operation {operation:key,argument:mask,select:|_:()|continuation(blueprint,next)}},
        Instruction::Child {expected,blueprint:child,next}=>mx::Node::Child {child:expected,
            dependencies:ports(bank[child as int].dependencies()),provisions:ports(bank[child as int].provisions()),
            root:Index {blueprint:child,pc:0},next:continuation(blueprint,next)},
    }
}
pub open spec fn programs(bank:Seq<Blueprint>)->mx::Programs<Port,u64,u64,(),Index> {
    |_:usize| |id:Index|instruction_node(bank,id.blueprint,
        if id.blueprint<bank.len() && id.pc<bank[id.blueprint as int].code().len() {bank[id.blueprint as int].code()[id.pc as int]}
        else {Instruction::Unit})
}
pub open spec fn bank_same(a:Seq<Blueprint>,b:Seq<Blueprint>)->bool {
    a.len()==b.len() && forall|i:int| #![trigger a[i]] #![trigger b[i]]
        0<=i<a.len() ==> a[i].same(&b[i])
}
pub open spec fn payload_equal(a:s::State<u64>,b:s::State<u64>)->bool {a.control==b.control && a.tables==b.tables}

pub proof fn run_payload(bank:Seq<Blueprint>,blueprint:usize,instruction:Instruction,a:s::State<u64>,b:s::State<u64>,actor:usize)
    requires payload_equal(a,b),
    ensures {
        let node=instruction_node(bank,blueprint,instruction);let x=mx::run(library(),node,a,actor);let y=mx::run(library(),node,b,actor);
        &&& x.is_some()==y.is_some()
        &&& x.is_some() ==> payload_equal(x.unwrap().state,y.unwrap().state) && x.unwrap().receipt==y.unwrap().receipt
            && x.unwrap().next==y.unwrap().next && x.unwrap().spawn==y.unwrap().spawn
    },
{match instruction {Instruction::Unit=>{},Instruction::Provide {..}=>{},Instruction::Xor {..}=>{},Instruction::Child {..}=>{}}}

pub proof fn undo_payload(receipt:Receipt,a:s::State<u64>,b:s::State<u64>)
    requires payload_equal(a,b),
    ensures mx::undo(receipt.model(),a).is_some()==mx::undo(receipt.model(),b).is_some(),
        mx::undo(receipt.model(),a).is_some() ==> payload_equal(mx::undo(receipt.model(),a).unwrap(),mx::undo(receipt.model(),b).unwrap()),
{match receipt.inverse {Inverse::Unit=>{},Inverse::Provision {..}=>{},Inverse::Xor {..}=>{},Inverse::Child {..}=>{}}}

pub open spec fn restore_receipts(receipts:Seq<Receipt>,a:s::State<u64>)->Option<s::State<u64>>
    decreases receipts.len(),
{
    if receipts.len()==0 {Some(a)} else {
        match mx::undo(receipts.last().model(),a) {None=>None,Some(b)=>restore_receipts(receipts.drop_last(),b)}
    }
}
pub proof fn restore_payload(receipts:Seq<Receipt>,a:s::State<u64>,b:s::State<u64>)
    requires payload_equal(a,b),
    ensures restore_receipts(receipts,a).is_some()==restore_receipts(receipts,b).is_some(),
        restore_receipts(receipts,a).is_some() ==> payload_equal(restore_receipts(receipts,a).unwrap(),restore_receipts(receipts,b).unwrap()),
    decreases receipts.len(),
{
    if receipts.len()>0 {
        undo_payload(receipts.last(),a,b);
        if mx::undo(receipts.last().model(),a).is_some() {
            restore_payload(receipts.drop_last(),mx::undo(receipts.last().model(),a).unwrap(),mx::undo(receipts.last().model(),b).unwrap());
        }
    }
}
pub proof fn restore_journal(history:Seq<mx::Entry<u64,Index>>,tokens:Seq<nat>,receipts:Seq<Receipt>,a:s::State<u64>,actor:usize)
    requires tokens.len()==receipts.len(),forall|i:int| #![trigger tokens[i]] 0<=i<tokens.len() ==> {
        tokens[i]<history.len() && history[tokens[i] as int].landed.receipt==receipts[i].model() && receipts[i].actor==actor
    },
    ensures mx::restore(history,tokens,a,actor)==restore_receipts(receipts,a),
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let token=tokens.last();assert(token==tokens[tokens.len()-1]);
        assert(history[token as int].landed.receipt==receipts.last().model());
        if mx::undo(receipts.last().model(),a).is_some() {
            restore_journal(history,tokens.drop_last(),receipts.drop_last(),mx::undo(receipts.last().model(),a).unwrap(),actor);
        }
    }
}

pub proof fn instruction_bank(a:Seq<Blueprint>,b:Seq<Blueprint>,blueprint:usize,instruction:Instruction)
    requires bank_same(a,b),match instruction {Instruction::Child {blueprint,..}=>blueprint<a.len(),_=>true},
    ensures instruction_node(a,blueprint,instruction)==instruction_node(b,blueprint,instruction),
{if let Instruction::Child {blueprint,..}=instruction {assert(a[blueprint as int].same(&b[blueprint as int]));}}

pub open spec fn outcome_rule(out:Outcome)->r::Rule {
    match out {Outcome::Advanced=>r::Rule::Iter,Outcome::Finished=>r::Rule::Finish,
        Outcome::Child {finished,..}=>if finished {r::Rule::Finish} else {r::Rule::Iter}}
}
proof fn landing_rule(bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>,actor:usize,rule:r::Rule)
    requires rule==r::Rule::Iter || rule==r::Rule::Finish,
        s::registered(a.state,actor),a.state.control.fibers[actor].phase==Phase::Loading,a.current[actor].is_some(),s::coherent(a.state,actor),
        mx::run(library(),programs(bank)(actor)(a.current[actor].unwrap()),a.state,actor).is_some(),
        (rule==r::Rule::Iter)==mx::run(library(),programs(bank)(actor)(a.current[actor].unwrap()),a.state,actor).unwrap().next.is_some(),
    ensures mx::step(library(),programs(bank),a,
        mx::land(library(),programs(bank),a,actor,if rule==r::Rule::Iter {Phase::Loading} else {Phase::Active}),actor,rule),
{if rule==r::Rule::Iter {} else {assert(rule==r::Rule::Finish);}}
pub proof fn program_member(bank:Seq<Blueprint>,actor:usize,id:Index)
    requires id.blueprint<bank.len(),id.pc<=bank[id.blueprint as int].code().len(),
        forall|i:int| #![trigger bank[i]] 0<=i<=id.blueprint ==> bank[i].valid(i as usize),
    ensures syntax::member(library(),programs(bank),actor,
        ports(bank[id.blueprint as int].dependencies()).union(ports(bank[id.blueprint as int].provisions())),
        ports(bank[id.blueprint as int].provisions()),id),
    decreases id.blueprint,bank[id.blueprint as int].code().len()-id.pc,
{
    let bp=bank[id.blueprint as int];let keys=ports(bp.dependencies()).union(ports(bp.provisions()));
    let provisions=ports(bp.provisions());let ps=programs(bank);
    assert(bp.valid(id.blueprint));reveal(Blueprint::valid);
    if id.pc<bp.code().len() {
        let instruction=bp.code()[id.pc as int];
        assert(instruction.valid(id.pc,bp.code.len(),id.blueprint,bp.dependencies(),bp.provisions()));
        let next=instruction.continuation();
        if next.is_some() {program_member(bank,actor,Index {blueprint:id.blueprint,pc:next.unwrap()});}
        if let Instruction::Child {expected,blueprint,..}=instruction {
            program_member(bank,expected,Index {blueprint,pc:0});
        }
    }
    assert(syntax::obligation(library(),ps(actor)(id),actor,keys,provisions,syntax::members(library(),ps)));
    syntax::constructor_member(library(),ps,actor,keys,provisions,id);
}

struct Row { blueprint:usize, current:Option<usize>, journal:Vec<Receipt> }
impl Row {
    spec fn same(&self,other:&Self)->bool {self.blueprint==other.blueprint && self.current==other.current && self.journal@==other.journal@}
    fn duplicate(&self)->(out:Self) ensures out.same(self),
    {Self {blueprint:self.blueprint,current:self.current,journal:copy_vec(&self.journal)}}
}

/// All mutable execution state is owned here. Neither the kernel nor mutable
/// tables or inverse handles escape this object.
pub struct MixedDriver {
    kernel:Kernel, blueprints:Vec<Blueprint>, rows:Vec<Row>, tables:Vec<Table>,
}

impl MixedDriver {
    pub closed spec fn control(&self)->r::State {self.kernel.paper()}
    pub closed spec fn table(&self,id:usize)->IMap<Port,u64> {self.tables[id as int].map()}
    pub closed spec fn journal(&self,id:usize)->Seq<Receipt> {self.rows[id as int].journal@}
    pub closed spec fn tables(&self)->IMap<usize,IMap<Port,u64>> {
        IMap::new(|n:usize|r::registered(self.control(),n),|n:usize|self.table(n))
    }
    /// Canonical input for primitive correspondence. Its control and tables
    /// are actual; whole-execution metadata is supplied by the simulation relation.
    pub closed spec fn primitive_state(&self)->s::State<u64> {
        s::State {control:self.control(),tables:self.tables(),
            effects:IMap::new(|n:usize|r::registered(self.control(),n),|_:usize|0nat),
            iterators:IMap::new(|n:usize|r::registered(self.control(),n),|_:usize|None),
            accumulators:IMap::new(|n:usize|r::registered(self.control(),n),|_:usize|Seq::empty())}
    }
    pub closed spec fn physical(&self,a:s::State<u64>)->bool {a.control==self.control() && a.tables==self.tables()}
    /// Each live concrete receipt corresponds to the history entry named by
    /// the source accumulator. Consumed source history may remain archived.
    pub closed spec fn represents(&self,bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>)->bool {
        &&& bank_same(self.blueprints@,bank) && self.physical(a.state)
        &&& a.roots.dom()==a.state.control.fibers.dom() && a.current.dom()==a.roots.dom()
        &&& a.state.effects.dom()==a.roots.dom() && a.state.iterators.dom()==a.roots.dom() && a.state.accumulators.dom()==a.roots.dom()
        &&& forall|n:usize| #![trigger a.roots[n]] #![trigger a.state.accumulators[n]] r::registered(self.control(),n) ==> {
            &&& n<self.rows.len()
            &&& a.roots[n]==(Index {blueprint:self.rows[n as int].blueprint,pc:0})
            &&& a.current[n]==continuation(self.rows[n as int].blueprint,self.rows[n as int].current)
            &&& a.state.effects[n]==0 && a.state.iterators[n]==crate::dependent_lift::marker(a.current[n])
            &&& a.state.accumulators[n].len()==self.journal(n).len()
            &&& forall|i:int| #![trigger a.state.accumulators[n][i]] 0<=i<self.journal(n).len() ==> {
                let token=a.state.accumulators[n][i];
                token<a.history.len() && a.history[token as int].landed.receipt==self.journal(n)[i].model()
            }
        }
    }
    /// Every successful transition has a source successor from every related
    /// well-formed source history; source validity is not supplied as an input trace.
    #[verifier::opaque]
    pub closed spec fn ack(&self,after:&Self,actor:usize,rule:r::Rule)->bool {
        forall|bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>| self.represents(bank,a) && mx::well_formed(library(),programs(bank),a)
            ==> exists|z:mx::Configuration<u64,Index>| mx::step(library(),programs(bank),a,z,actor,rule) && after.represents(bank,z)
    }
    closed spec fn administrative(&self,a:mx::Configuration<u64,Index>,actor:usize,rule:r::Rule)->mx::Configuration<u64,Index> {
        match rule {
            r::Rule::Insert=>mx::Configuration {
                state:s::State {control:self.control(),tables:self.tables(),effects:a.state.effects.insert(actor,0),
                    iterators:a.state.iterators.insert(actor,None),accumulators:a.state.accumulators.insert(actor,Seq::empty())},
                roots:a.roots.insert(actor,Index {blueprint:self.rows[actor as int].blueprint,pc:0}),
                current:a.current.insert(actor,None),history:a.history},
            r::Rule::Remove=>mx::Configuration {state:s::erase(a.state,actor),roots:a.roots.remove(actor),current:a.current.remove(actor),history:a.history},
            r::Rule::Retire=>mx::Configuration {state:s::State {control:self.control(),..a.state},..a},
            r::Rule::Begin=>mx::edit(a,actor,Phase::Loading,self.control().fibers[actor].committed,Some(a.roots[actor]),Seq::empty()),
            _=>mx::edit(a,actor,Phase::Unloading,a.state.control.fibers[actor].committed,None,a.state.accumulators[actor]),
        }
    }
    closed spec fn unreferenced(&self,id:usize)->bool {
        forall|n:int,i:int| #![trigger self.rows[n].journal[i]] 0<=n<self.rows.len() && 0<=i<self.rows[n].journal.len()
            ==> self.rows[n].journal[i].inverse!=(Inverse::Child {child:id})
    }
    #[verifier::spinoff_prover]
    #[verifier::rlimit(20)]
    proof fn administrative_simulation(&self,initial:&Self,actor:usize,rule:r::Rule)
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
        ensures initial.ack(self,actor,rule),
    {
        reveal(MixedDriver::ack);library_theory();
        assert forall|bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>| initial.represents(bank,a) && mx::well_formed(library(),programs(bank),a)
            implies exists|z:mx::Configuration<u64,Index>| mx::step(library(),programs(bank),a,z,actor,rule) && self.represents(bank,z) by {
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
                        assert(initial.rows[n as int].journal[i].inverse!=(Inverse::Child {child:actor}));
                        match initial.journal(n)[i].inverse {Inverse::Child {child}=>{assert(child!=actor);},_=>{},}
                    }
                }
            }
            assert(mx::step(library(),programs(bank),a,z,actor,rule));
            mx::state_preservation(|_:Port,x:u64,y:u64|x==y,library(),programs(bank),a,z,actor,rule);
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
                &&& z.current[n]==continuation(self.rows[n as int].blueprint,self.rows[n as int].current)
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
    #[verifier::opaque]
    pub closed spec fn step_ack(&self,after:&Self,actor:usize,outcome:Outcome)->bool {
        forall|bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>| self.represents(bank,a) && mx::well_formed(library(),programs(bank),a) ==> {
            let rule=outcome_rule(outcome);let z=mx::land(library(),programs(bank),a,actor,if rule==r::Rule::Iter {Phase::Loading} else {Phase::Active});
            mx::step(library(),programs(bank),a,z,actor,rule) && after.represents(bank,z)
        }
    }
    pub proof fn landing_ack(&self,after:&Self,actor:usize,outcome:Outcome)
        requires self.step_ack(after,actor,outcome),
        ensures self.ack(after,actor,outcome_rule(outcome)),
    {
        reveal(MixedDriver::step_ack);reveal(MixedDriver::ack);
        assert forall|bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>| self.represents(bank,a) && mx::well_formed(library(),programs(bank),a)
            implies exists|z:mx::Configuration<u64,Index>| mx::step(library(),programs(bank),a,z,actor,outcome_rule(outcome)) && after.represents(bank,z) by {
            let rule=outcome_rule(outcome);
            let z=mx::land(library(),programs(bank),a,actor,if rule==r::Rule::Iter {Phase::Loading} else {Phase::Active});
            assert(mx::step(library(),programs(bank),a,z,actor,rule) && after.represents(bank,z));
        }
    }
    proof fn table_declaration(&self,actor:usize,key:Port)
        requires self.wf(),r::registered(self.control(),actor),
        ensures self.tables[actor as int].find(key).is_some()==self.control().fibers[actor].provisions.contains(key),
    {
        self.kernel.paper_observations(actor);self.row_bounds(actor);
        assert(self.layout(actor as int));
        let table=self.tables[actor as int];let bp=self.blueprints[self.rows[actor as int].blueprint as int];
        if table.find(key).is_some() {
            let i=table.find(key).unwrap();assert(table.slots[i as int].key==key);
            assert(bp.provisions[i as int]==key);assert(bp.provisions@.contains(key));
        }
        if self.control().fibers[actor].provisions.contains(key) {
            let i=choose|i:int|0<=i<bp.provisions.len() && bp.provisions[i]==key;
            assert(table.slots[i].key==key);
            assert(exists|i:int|0<=i<table.slots.len() && table.slots[i].key==key);
        }
    }
    proof fn canonical_equal(&self,other:&Self)
        requires self.control()==other.control(),self.tables@==other.tables@,
        ensures self.primitive_state()==other.primitive_state(),
    {
        assert(self.tables() =~= other.tables());
        assert(self.primitive_state().effects =~= other.primitive_state().effects);
        assert(self.primitive_state().iterators =~= other.primitive_state().iterators);
        assert(self.primitive_state().accumulators =~= other.primitive_state().accumulators);
    }
    proof fn paper_total(&self,a:s::State<u64>)
        requires self.wf(),self.physical(a),
        ensures s::total_active(a),
    {
        assert forall|n:usize| r::registered(a.control,n) && a.control.fibers[n].phase==Phase::Active
            implies a.tables[n].dom()==a.control.fibers[n].provisions by {
            self.kernel.paper_observations(n);self.row_bounds(n);
            assert(a.tables[n].dom() =~= a.control.fibers[n].provisions) by {
                assert forall|key:Port| a.tables[n].dom().contains(key)==a.control.fibers[n].provisions.contains(key) by {
                    self.table_declaration(n,key);
                    if self.tables[n as int].find(key).is_some() {
                        let i=self.tables[n as int].find(key).unwrap();
                        assert(self.tables[n as int].view()[i as int].value.is_some());
                    }
                }
            }
        }
    }
    fn write_slot(&mut self,provider:usize,index:usize,value:Option<u64>)
        requires old(self).wf(),r::registered(old(self).control(),provider),provider<old(self).tables.len(),
            index<old(self).tables[provider as int].view().len(),
            value.is_none() ==> old(self).control().fibers[provider].phase!=Phase::Active,
        ensures final(self).wf(),final(self).control()==old(self).control(),final(self).rows@==old(self).rows@,
            final(self).blueprints@==old(self).blueprints@,
            final(self).physical(projection::update_slot(old(self).primitive_state(),provider,old(self).tables[provider as int].view()[index as int].key,value)),
    {
        let ghost prior=*self;
        self.tables[provider].put(index,value);
        let ghost key=prior.tables[provider as int].view()[index as int].key;
        let ghost expected=projection::update_slot(prior.primitive_state(),provider,key,value);
        assert(self.tables() =~= expected.tables) by {
            assert forall|n:usize| self.tables().dom().contains(n) implies self.tables()[n]==expected.tables[n] by {
                if n!=provider {assert(self.tables[n as int]==prior.tables[n as int]);}
            }
        }
    }
    pub closed spec fn bank_valid(&self,rank:usize)->bool {
        rank<self.blueprints.len() && forall|i:int| #![trigger self.blueprints[i]] 0<=i<=rank ==> self.blueprints[i].valid(i as usize)
    }
    closed spec fn layout(&self,id:int)->bool {
        let bp=self.blueprints[self.rows[id].blueprint as int];
        &&& self.tables[id].view().len()==bp.provisions@.len()
        &&& (forall|i:int| 0<=i<bp.provisions.len() ==> self.tables[id].view()[i].key==bp.provisions[i])
        &&& (r::registered(self.control(),id as usize) ==> {
            self.control().fibers[id as usize].provisions==ISet::new(|p:Port|bp.provisions@.contains(p))
                && self.control().fibers[id as usize].dependencies==ISet::new(|p:Port|bp.dependencies@.contains(p))
        })
    }
    pub closed spec fn wf(&self)->bool {
        self.kernel.wf() && self.rows.len()==self.kernel.next_id() && self.tables.len()==self.rows.len()
        && (forall|i:int| #![trigger self.rows[i]] #![trigger self.tables[i]]
            0<=i<self.rows.len() ==> self.rows[i].blueprint<self.blueprints.len() && self.tables[i].unique())
        && (forall|i:int| 0<=i<self.rows.len() && self.rows[i].current.is_some()
            ==> self.rows[i].current.unwrap()<=self.blueprints[self.rows[i].blueprint as int].code.len())
        && (forall|i:int| #![trigger self.rows[i]] #![trigger self.tables[i]]
            0<=i<self.rows.len() ==> self.bank_valid(self.rows[i].blueprint) && self.layout(i))
        && (forall|n:usize,i:int| #![trigger self.tables[n as int].view()[i]]
            r::registered(self.control(),n) && self.control().fibers[n].phase==Phase::Active
                && 0<=i<self.tables[n as int].view().len() ==> self.tables[n as int].view()[i].value.is_some())
        && (forall|n:int,i:int| #![trigger self.rows[n].journal[i]] 0<=n<self.rows.len() && 0<=i<self.rows[n].journal.len()
            ==> self.rows[n].journal[i].actor==n)
    }
    proof fn row_bounds(&self,i:usize)
        requires self.wf(),i<self.rows.len(),
        ensures self.rows[i as int].blueprint<self.blueprints.len(),self.tables[i as int].unique(),
            self.rows[i as int].current.is_some() ==> self.rows[i as int].current.unwrap()<=self.blueprints[self.rows[i as int].blueprint as int].code.len(),
    {
        reveal(MixedDriver::wf);
        assert(forall|j:int| 0<=j<self.rows.len() ==> self.rows[j].blueprint<self.blueprints.len() && self.tables[j].unique());
        assert(0<=(i as int)<self.rows.len());
        assert(self.rows[i as int].blueprint<self.blueprints.len() && self.tables[i as int].unique());
    }
    pub closed spec fn observation(&self)->(r::State,Seq<Seq<Slot>>,Seq<Option<usize>>,Seq<Seq<Receipt>>) {
        (self.control(),Seq::new(self.tables@.len(),|i:int|self.tables[i].view()),
            Seq::new(self.rows@.len(),|i:int|self.rows[i].current),Seq::new(self.rows@.len(),|i:int|self.rows[i].journal@))
    }
    /// Full logical machine equality, including installed code, blueprint
    /// selections, generations, and retained journals. Vector capacity is irrelevant.
    pub closed spec fn same(&self,other:&Self)->bool {
        &&& self.kernel.unchanged(&other.kernel)
        &&& self.blueprints.len()==other.blueprints.len() && self.rows.len()==other.rows.len() && self.tables.len()==other.tables.len()
        &&& forall|i:int| 0<=i<self.blueprints.len() ==> self.blueprints[i].same(&other.blueprints[i])
        &&& forall|i:int| 0<=i<self.rows.len() ==> self.rows[i].same(&other.rows[i]) && self.tables[i].view()==other.tables[i].view()
    }

    pub fn new(blueprints:Vec<Blueprint>)->(out:Self)
        ensures out.wf(),out.control().fibers.dom().is_empty(),out.represents(blueprints@,mx::empty()),
    {
        let out=Self {kernel:Kernel::new(),blueprints,rows:Vec::new(),tables:Vec::new()};
        assert(out.control().fibers =~= IMap::empty());assert(out.tables() =~= IMap::empty());out
    }

    fn duplicate(&self)->(out:Self)
        requires self.wf(),
        ensures out.same(self),out.wf(),out.control()==self.control(),out.observation()==self.observation(),
            out.rows.len()==self.rows.len(),out.blueprints.len()==self.blueprints.len(),
            forall|i:int| 0<=i<self.rows.len() ==> out.rows[i].same(&self.rows[i]),
            forall|bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>| out.represents(bank,a)==self.represents(bank,a),
    {
        let mut blueprints:Vec<Blueprint>=Vec::new();let mut i=0;
        while i<self.blueprints.len()
            invariant i<=self.blueprints.len(),blueprints.len()==i,
                forall|j:int| 0<=j<i ==> blueprints[j].same(&self.blueprints[j]),
            decreases self.blueprints.len()-i,
        {blueprints.push(self.blueprints[i].duplicate());i+=1;}
        let mut rows:Vec<Row>=Vec::new();i=0;
        while i<self.rows.len()
            invariant i<=self.rows.len(),rows.len()==i,forall|j:int| 0<=j<i ==> rows[j].same(&self.rows[j]),
            decreases self.rows.len()-i,
        {rows.push(self.rows[i].duplicate());i+=1;}
        let mut tables:Vec<Table>=Vec::new();i=0;
        while i<self.tables.len()
            invariant i<=self.tables.len(),tables.len()==i,forall|j:int| 0<=j<i ==> tables[j].view()==self.tables[j].view(),
            decreases self.tables.len()-i,
        {tables.push(self.tables[i].duplicate());i+=1;}
        let out=Self {kernel:copy_kernel(&self.kernel),blueprints,rows,tables};
        assert(out.same(self));
        assert(out.observation().1 =~= self.observation().1);
        assert(out.observation().2 =~= self.observation().2);
        assert(out.observation().3 =~= self.observation().3);
        assert(out.tables() =~= self.tables()) by {
            assert forall|n:usize| r::registered(self.control(),n) implies out.table(n)==self.table(n) by {
                self.kernel.paper_observations(n);self.row_bounds(n);out.row_bounds(n);
                self.tables[n as int].same_map(&out.tables[n as int]);
            }
        }
        assert forall|bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>| out.represents(bank,a)==self.represents(bank,a) by { }
        out
    }

    fn registered(&self,id:usize)->(yes:bool)
        requires self.wf(),
        ensures yes==r::registered(self.control(),id),yes ==> id<self.rows.len(),
    {
        proof {self.kernel.paper_observations(id);}
        self.kernel.contains(id)
    }

    fn check_blueprints(&self,rank:usize)->(yes:bool)
        ensures yes==self.bank_valid(rank),
    {
        if rank>=self.blueprints.len() {return false;}
        let mut i=0;
        while i<=rank
            invariant i<=rank+1,rank<self.blueprints.len(),forall|j:int| 0<=j<i ==> self.blueprints[j].valid(j as usize),
            decreases rank+1-i,
        {if !self.blueprints[i].validate(i) {return false;}i+=1;}
        true
    }

    /// Install a blueprint without exposing its mutable code or declarations.
    pub fn insert(&mut self,parent:Option<usize>,blueprint:usize)->(out:Result<usize,DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_err() ==> final(self).observation()==old(self).observation() && final(self).same(old(self)),
            out.is_ok() ==> r::step(old(self).control(),final(self).control(),out.unwrap(),r::Rule::Insert)
                && old(self).ack(final(self),out.unwrap(),r::Rule::Insert),
    {
        let mut draft=self.duplicate();
        let ghost initial=draft;
        match draft.insert_inner(parent,blueprint) {
            Err(e)=>Err(e),Ok(id)=>{proof {draft.administrative_simulation(&initial,id,r::Rule::Insert);reveal(MixedDriver::ack);}*self=draft;Ok(id)},
        }
    }

    fn insert_inner(&mut self,parent:Option<usize>,blueprint:usize)->(out:Result<usize,DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).blueprints@==old(self).blueprints@,
            final(self).rows.len()>=old(self).rows.len(),
            forall|i:int| 0<=i<old(self).rows.len() ==> final(self).rows[i]==old(self).rows[i] && final(self).tables[i]==old(self).tables[i],
            out.is_ok() ==> r::step(old(self).control(),final(self).control(),out.unwrap(),r::Rule::Insert)
                && out.unwrap()==old(self).rows.len() && final(self).rows.len()==old(self).rows.len()+1
                && final(self).rows[out.unwrap() as int].blueprint==blueprint && final(self).table(out.unwrap()).is_empty()
                && final(self).rows[out.unwrap() as int].current.is_none() && final(self).rows[out.unwrap() as int].journal.len()==0
                && final(self).control().fibers[out.unwrap()].parent==parent,
    {
        if blueprint>=self.blueprints.len() {return Err(DriverError::InvalidBlueprint);}
        if !self.check_blueprints(blueprint) {return Err(DriverError::InvalidInstruction);}
        let dependencies=copy_vec(&self.blueprints[blueprint].dependencies);
        let provisions=copy_vec(&self.blueprints[blueprint].provisions);
        let mut slots:Vec<Slot>=Vec::new();let mut i=0;
        while i<provisions.len()
            invariant self.wf(),i<=provisions.len(),slots.len()==i,
                self.bank_valid(blueprint),provisions@==self.blueprints[blueprint as int].provisions@,
                dependencies@==self.blueprints[blueprint as int].dependencies@,
                forall|j:int| 0<=j<i ==> slots[j]==(Slot {key:provisions[j],value:None}),
                forall|j:int,k:int| 0<=j<i && 0<=k<i && slots[j].key==slots[k].key ==> j==k,
            decreases provisions.len()-i,
        {
            let mut j=0;
            while j<i
                invariant self.wf(),j<=i,i<provisions.len(),slots.len()==i,
                    self.bank_valid(blueprint),provisions@==self.blueprints[blueprint as int].provisions@,
                    dependencies@==self.blueprints[blueprint as int].dependencies@,
                    forall|k:int| 0<=k<i ==> slots[k].key==provisions[k],
                    forall|k:int| 0<=k<j ==> provisions[k]!=provisions[i as int],
                decreases i-j,
            {if provisions[j]==provisions[i] {return Err(DriverError::InvalidBlueprint);}j+=1;}
            slots.push(Slot {key:provisions[i],value:None});i+=1;
        }
        let result=self.kernel.insert(parent,dependencies,provisions);
        match result {
            Err(e)=>{proof {self.kernel.unchanged_observations(&old(self).kernel);}Err(DriverError::Kernel(e))},
            Ok(id)=>{
                self.rows.push(Row {blueprint,current:None,journal:Vec::new()});self.tables.push(Table {slots});
                assert(self.control().fibers[id].provisions =~= ports(self.blueprints[blueprint as int].provisions()));
                assert(self.control().fibers[id].dependencies =~= ports(self.blueprints[blueprint as int].dependencies()));
                assert forall|j:int| 0<=j<self.rows.len() implies self.rows[j].blueprint<self.blueprints.len() && self.tables[j].unique() by {
                    if j<id {old(self).row_bounds(j as usize);assert(self.rows[j]==old(self).rows[j]);assert(self.tables[j]==old(self).tables[j]);}
                }
                assert forall|j:int| 0<=j<self.rows.len() && self.rows[j].current.is_some() implies
                    self.rows[j].current.unwrap()<=self.blueprints[self.rows[j].blueprint as int].code.len() by {
                    if j<id {assert(self.rows[j]==old(self).rows[j]);}
                }
                assert forall|j:int| 0<=j<self.rows.len() implies self.bank_valid(self.rows[j].blueprint) && self.layout(j) by {
                    if j<id {
                        assert(self.rows[j]==old(self).rows[j]);assert(self.tables[j]==old(self).tables[j]);
                        assert(old(self).layout(j));
                        assert(r::registered(self.control(),j as usize)==r::registered(old(self).control(),j as usize));
                        if r::registered(self.control(),j as usize) {assert(self.control().fibers[j as usize]==old(self).control().fibers[j as usize]);}
                    }
                }
                assert(self.table(id).dom().is_empty());
                Ok(id)
            },
        }
    }

    pub fn begin(&mut self,id:usize)->(out:Result<(),DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_err() ==> final(self).observation()==old(self).observation() && final(self).same(old(self)),
            out.is_ok() ==> r::step(old(self).control(),final(self).control(),id,r::Rule::Begin)
                && final(self).journal(id).len()==0 && old(self).ack(final(self),id,r::Rule::Begin),
    {
        if !self.registered(id) {return Err(DriverError::Unknown);}
        if !self.rows[id].journal.is_empty() {return Err(DriverError::Retained);}
        let mut draft=self.duplicate();
        let ghost initial=draft;
        match draft.kernel.begin(id) {
            Err(e)=>Err(DriverError::Kernel(e)),
            Ok(())=>{draft.rows[id].current=Some(0);proof {draft.administrative_simulation(&initial,id,r::Rule::Begin);reveal(MixedDriver::ack);}*self=draft;Ok(())},
        }
    }

    pub fn retire(&mut self,id:usize)->(out:Result<(),DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_err() ==> final(self).observation()==old(self).observation() && final(self).same(old(self)),
            out.is_ok() ==> r::step(old(self).control(),final(self).control(),id,r::Rule::Retire) && old(self).ack(final(self),id,r::Rule::Retire),
    {
        let mut draft=self.duplicate();
        let ghost initial=draft;
        match draft.kernel.retire(id) {Err(e)=>Err(DriverError::Kernel(e)),Ok(())=>{proof {draft.administrative_simulation(&initial,id,r::Rule::Retire);reveal(MixedDriver::ack);}*self=draft;Ok(())}}
    }

    pub fn depart(&mut self,id:usize)->(out:Result<(),DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_err() ==> final(self).observation()==old(self).observation() && final(self).same(old(self)),
            out.is_ok() ==> r::step(old(self).control(),final(self).control(),id,
                if old(self).control().fibers[id].phase==Phase::Loading {r::Rule::Divert} else {r::Rule::Leave})
                && old(self).ack(final(self),id,if old(self).control().fibers[id].phase==Phase::Loading {r::Rule::Divert} else {r::Rule::Leave}),
    {
        if !self.registered(id) {return Err(DriverError::Unknown);}
        let mut draft=self.duplicate();
        let ghost initial=draft;
        match draft.kernel.leave_if_changed(id) {
            Err(e)=>Err(DriverError::Kernel(e)),
            Ok(())=>{draft.rows[id].current=None;proof {draft.administrative_simulation(&initial,id,if initial.control().fibers[id].phase==Phase::Loading {r::Rule::Divert} else {r::Rule::Leave});reveal(MixedDriver::ack);}*self=draft;Ok(())},
        }
    }

    /// Resolve only the installed episode identity. Retirement does not cause
    /// this lookup to redirect an operation or inverse to a replacement.
    fn provider(&self,actor:usize,key:Port)->(out:Result<usize,DriverError>)
        requires self.wf(),actor<self.rows.len(),r::registered(self.control(),actor),
        ensures out.is_ok() ==> out.unwrap()<self.tables.len() && r::registered(self.control(),out.unwrap())
            && lift::resolve(self.primitive_state(),actor,key)==Some(out.unwrap()),
    {
        proof {self.kernel.refines_paper();self.table_declaration(actor,key);}
        if self.tables[actor].locate(key).is_some() {return Ok(actor);}
        let bindings=self.kernel.committed(actor);let mut i=0;
        while i<bindings.len()
            invariant self.wf(),r::well_formed(self.control()),actor<self.rows.len(),r::registered(self.control(),actor),
                !self.control().fibers[actor].provisions.contains(key),i<=bindings.len(),
                self.control().fibers[actor].committed==ports_bindings(bindings@),
            decreases bindings.len()-i,
        {
            let b=bindings[i];
            if b.key==key.key && b.realm==key.realm {
                if !self.registered(b.provider) {return Err(DriverError::MissingBinding);}
                proof {
                    assert(bindings@.contains(b));assert(self.control().fibers[actor].committed.contains(b));
                    assert(self.control().fibers[actor].dependencies.contains(key));
                    assert(lift::names_key(b,key));
                    assert(exists|c:crate::Binding|self.control().fibers[actor].committed.contains(c) && lift::names_key(c,key));
                    let chosen=choose|c:crate::Binding|self.control().fibers[actor].committed.contains(c) && lift::names_key(c,key);
                    assert(chosen.key==b.key && chosen.realm==b.realm);
                    assert(chosen.provider==b.provider);
                }
                return Ok(b.provider);
            }
            i+=1;
        }
        Err(DriverError::MissingBinding)
    }

    fn provided(&self,id:usize)->(yes:bool)
        requires self.wf(),id<self.tables.len(),
        ensures yes==(forall|i:int| 0<=i<self.tables[id as int].view().len()
            ==> self.tables[id as int].view()[i].value.is_some()),
    {
        let mut i=0;
        while i<self.tables[id].slots.len()
            invariant id<self.tables.len(),i<=self.tables[id as int].slots.len(),
                forall|j:int| 0<=j<i ==> self.tables[id as int].slots[j].value.is_some(),
            decreases self.tables[id as int].slots.len()-i,
        {if self.tables[id].slots[i].value.is_none() {return false;}i+=1;}
        true
    }

    /// A complete synchronous landing; the caller never supplies a replacement
    /// payload, continuation, or inverse after the instruction is installed.
    pub fn step(&mut self,actor:usize)->(out:Result<Outcome,DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_err() ==> final(self).observation()==old(self).observation() && final(self).same(old(self)),
            out.is_ok() ==> final(self).journal(actor).len()==old(self).journal(actor).len()+1
                && final(self).journal(actor).last().actor==actor
                && old(self).step_ack(final(self),actor,out.unwrap())
                && old(self).ack(final(self),actor,outcome_rule(out.unwrap())),
    {
        let ghost initial=*self;
        let mut draft=self.duplicate();
        match draft.step_inner(actor) {Err(e)=>Err(e),Ok(outcome)=>{
            proof {reveal(MixedDriver::step_ack);initial.landing_ack(&draft,actor,outcome);}
            *self=draft;Ok(outcome)
        }}
    }

    /// The executable primitive interpreter, directly related to the existing
    /// mixed grammar. This runs table writes and real kernel child insertion.
    fn execute(&mut self,actor:usize,_blueprint:usize,instruction:Instruction)->(out:Result<Receipt,DriverError>)
        requires old(self).wf(),actor<old(self).rows.len(),r::registered(old(self).control(),actor),
            old(self).control().fibers[actor].phase==Phase::Loading,
        ensures final(self).wf(),final(self).blueprints@==old(self).blueprints@,
            final(self).rows.len()>=old(self).rows.len(),
            forall|i:int| 0<=i<old(self).rows.len() ==> final(self).rows[i]==old(self).rows[i],
            out.is_ok() ==> {
                let y=mx::run(library(),instruction_node(old(self).blueprints@,_blueprint,instruction),old(self).primitive_state(),actor);
                &&& y.is_some() && final(self).physical(y.unwrap().state) && out.unwrap().model()==y.unwrap().receipt
                &&& out.unwrap().actor==actor
                &&& match instruction {
                    Instruction::Child {expected,blueprint,..}=>expected==old(self).rows.len() && final(self).rows.len()==old(self).rows.len()+1
                        && final(self).rows[old(self).rows.len() as int].blueprint==blueprint
                        && final(self).rows[old(self).rows.len() as int].current.is_none()
                        && final(self).rows[old(self).rows.len() as int].journal.len()==0,
                    _=>final(self).rows.len()==old(self).rows.len(),
                }
            },
    {
        let ghost before=*self;
        let inverse=match instruction {
            Instruction::Unit=>Inverse::Unit,
            Instruction::Provide {key,value,..}=>{
                proof {self.table_declaration(actor,key);}
                let index=match self.tables[actor].locate(key) {Some(i)=>i,None=>return Err(DriverError::MissingBinding)};
                if self.tables[actor].slots[index].value.is_some() {return Err(DriverError::AlreadyProvided);}
                self.write_slot(actor,index,Some(value));
                Inverse::Provision {key}
            },
            Instruction::Xor {key,mask,..}=>{
                let provider=self.provider(actor,key)?;
                let index=match self.tables[provider].locate(key) {Some(i)=>i,None=>return Err(DriverError::MissingValue)};
                let value=match self.tables[provider].slots[index].value {Some(v)=>v,None=>return Err(DriverError::MissingValue)};
                self.write_slot(provider,index,Some(value^mask));
                Inverse::Xor {provider,key,mask}
            },
            Instruction::Child {expected,blueprint,..}=>{
                if expected!=self.rows.len() {return Err(DriverError::UnexpectedChild);}
                let child=self.insert_inner(Some(actor),blueprint)?;
                proof {
                    let target=mx::create(before.primitive_state(),actor,child,
                        ports(before.blueprints[blueprint as int].dependencies()),ports(before.blueprints[blueprint as int].provisions()));
                    assert(self.layout(child as int));
                    assert(self.control().fibers[child].provisions==ports(before.blueprints[blueprint as int].provisions()));
                    assert(self.control().fibers[child].dependencies==ports(before.blueprints[blueprint as int].dependencies()));
                    assert(self.control().fibers[child]==target.control.fibers[child]);
                    assert(r::frame(before.control(),self.control(),child));
                    assert(self.control().fibers.dom() =~= target.control.fibers.dom()) by {
                        assert forall|n:usize| self.control().fibers.dom().contains(n)==target.control.fibers.dom().contains(n) by {
                            if n!=child {assert(r::registered(self.control(),n)==r::registered(before.control(),n));}
                        }
                    }
                    assert(self.control().fibers =~= target.control.fibers) by {
                        assert forall|n:usize| r::registered(self.control(),n) implies self.control().fibers[n]==target.control.fibers[n] by {
                            if n!=child {assert(self.control().fibers[n]==before.control().fibers[n]);}
                        }
                    }
                    assert(self.tables() =~= target.tables) by {
                        assert forall|n:usize| self.tables().dom().contains(n) implies self.tables()[n]==target.tables[n] by {
                            if n!=child {assert(self.tables[n as int]==before.tables[n as int]);}
                        }
                    }
                    assert(self.physical(target));
                }
                Inverse::Child {child}
            },
        };
        Ok(Receipt {actor,inverse})
    }

    fn commit_landing(&mut self,actor:usize,receipt:Receipt,next:Option<usize>)->(out:Result<(),DriverError>)
        requires old(self).wf(),actor<old(self).rows.len(),r::registered(old(self).control(),actor),
            old(self).control().fibers[actor].phase==Phase::Loading,receipt.actor==actor,
            next.is_some() ==> next.unwrap()<=old(self).blueprints[old(self).rows[actor as int].blueprint as int].code.len(),
        ensures final(self).wf(),final(self).rows.len()==old(self).rows.len(),
            final(self).tables@==old(self).tables@,final(self).blueprints@==old(self).blueprints@,
            out.is_ok() ==> {
                &&& final(self).rows[actor as int].blueprint==old(self).rows[actor as int].blueprint
                &&& final(self).rows[actor as int].current==next
                &&& final(self).journal(actor)==old(self).journal(actor).push(receipt)
                &&& forall|i:int| 0<=i<old(self).rows.len() && i!=actor ==> final(self).rows[i]==old(self).rows[i]
                &&& (next.is_none() ==> r::step(old(self).control(),final(self).control(),actor,r::Rule::Finish))
                &&& (next.is_some() ==> old(self).control()==final(self).control())
            },
    {
        if next.is_none() {
            if !self.provided(actor) {return Err(DriverError::IncompleteProvision);}
            if let Err(e)=self.kernel.finish(actor) {return Err(DriverError::Kernel(e));}
        }
        self.rows[actor].current=next;
        self.rows[actor].journal.push(receipt);
        Ok(())
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(60)]
    fn step_inner(&mut self,actor:usize)->(out:Result<Outcome,DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_ok() ==> actor<old(self).rows.len() && final(self).journal(actor).len()==old(self).journal(actor).len()+1
            && final(self).journal(actor).last().actor==actor && old(self).step_ack(final(self),actor,out.unwrap()),
    {
        let ghost initial=*self;
        if !self.registered(actor) {return Err(DriverError::Unknown);}
        if let Err(e)=self.kernel.check_iteration(actor) {return Err(DriverError::Kernel(e));}
        proof {self.row_bounds(actor);}
        let pc=match self.rows[actor].current {Some(pc)=>pc,None=>return Err(DriverError::InvalidInstruction)};
        let blueprint=self.rows[actor].blueprint;
        let length=self.blueprints[blueprint].code.len();
        let instruction=if pc==length {Instruction::Unit} else {self.blueprints[blueprint].code[pc]};
        let next=match instruction {Instruction::Unit=>None,Instruction::Provide {next,..}=>next,
            Instruction::Xor {next,..}=>next,Instruction::Child {next,..}=>next};
        if let Some(next)=next {if next<=pc || next>length {return Err(DriverError::InvalidInstruction);}}
        let receipt=self.execute(actor,blueprint,instruction)?;
        let ghost landed=*self;
        self.commit_landing(actor,receipt,next)?;
        let outcome=match receipt.inverse {
            Inverse::Child {child}=>Outcome::Child {child,finished:next.is_none()},
            _=>if next.is_none() {Outcome::Finished} else {Outcome::Advanced},
        };
        proof {
            self.landing_simulation(&initial,&landed,actor,blueprint,pc,instruction,receipt,next,outcome);
        }
        Ok(outcome)
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(30)]
    proof fn landing_simulation(&self,initial:&Self,landed:&Self,actor:usize,blueprint:usize,pc:usize,
        instruction:Instruction,receipt:Receipt,next:Option<usize>,outcome:Outcome)
        requires self.wf(),initial.wf(),landed.wf(),actor<initial.rows.len(),
            r::registered(initial.control(),actor),initial.control().fibers[actor].phase==Phase::Loading,r::coherent(initial.control(),actor),
            initial.rows[actor as int].blueprint==blueprint,initial.rows[actor as int].current==Some(pc),
            instruction==if pc==initial.blueprints[blueprint as int].code.len() {Instruction::Unit} else {initial.blueprints[blueprint as int].code[pc as int]},
            next==instruction.continuation(),outcome_rule(outcome)==if next.is_some() {r::Rule::Iter} else {r::Rule::Finish},
            initial.blueprints@==landed.blueprints@,self.blueprints@==initial.blueprints@,
            {
                let y=mx::run(library(),instruction_node(initial.blueprints@,blueprint,instruction),initial.primitive_state(),actor);
                y.is_some() && landed.physical(y.unwrap().state) && receipt.model()==y.unwrap().receipt
            },
            landed.rows.len()>=initial.rows.len(),self.rows.len()==landed.rows.len(),self.tables@==landed.tables@,
            forall|i:int| 0<=i<initial.rows.len() ==> landed.rows[i]==initial.rows[i],
            forall|i:int| 0<=i<self.rows.len() && i!=actor ==> self.rows[i]==landed.rows[i],
            self.rows[actor as int].blueprint==blueprint,self.rows[actor as int].current==next,
            self.journal(actor)==initial.journal(actor).push(receipt),
            match instruction {
                Instruction::Child {expected,blueprint,..}=>expected==initial.rows.len() && landed.rows.len()==initial.rows.len()+1
                    && landed.rows[initial.rows.len() as int].blueprint==blueprint
                    && landed.rows[initial.rows.len() as int].current.is_none()
                    && landed.rows[initial.rows.len() as int].journal.len()==0,
                _=>landed.rows.len()==initial.rows.len(),
            },
            next.is_none() ==> r::step(landed.control(),self.control(),actor,r::Rule::Finish),
            next.is_some() ==> self.control()==landed.control(),
        ensures initial.step_ack(self,actor,outcome),
    {
        reveal(MixedDriver::step_ack);
        let length=initial.blueprints[blueprint as int].code.len();
        library_theory();
            assert forall|bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>| initial.represents(bank,a) && mx::well_formed(library(),programs(bank),a) implies {
                let rule=outcome_rule(outcome);let z=mx::land(library(),programs(bank),a,actor,if rule==r::Rule::Iter {Phase::Loading} else {Phase::Active});
                mx::step(library(),programs(bank),a,z,actor,rule) && self.represents(bank,z)
            } by {
                let rule=outcome_rule(outcome);let phase=if rule==r::Rule::Iter {Phase::Loading} else {Phase::Active};
                let z=mx::land(library(),programs(bank),a,actor,phase);
                assert(a.current[actor]==Some(Index {blueprint,pc}));
                assert(bank[blueprint as int].same(&initial.blueprints[blueprint as int]));
                assert(instruction.valid(pc,length,blueprint,initial.blueprints[blueprint as int].dependencies(),initial.blueprints[blueprint as int].provisions()));
                instruction_bank(initial.blueprints@,bank,blueprint,instruction);
                assert(programs(bank)(actor)(a.current[actor].unwrap())==instruction_node(initial.blueprints@,blueprint,instruction));
                run_payload(initial.blueprints@,blueprint,instruction,initial.primitive_state(),a.state,actor);
                let y=mx::run(library(),programs(bank)(actor)(a.current[actor].unwrap()),a.state,actor).unwrap();
                assert(landed.physical(y.state));assert(y.receipt==receipt.model());
                assert(y.next==continuation(blueprint,next));
                initial.paper_total(a.state);
                s::total_targets_agree(a.state,actor,a.state.control.fibers[actor].committed);
                landing_rule(bank,a,actor,rule);
                mx::frame(|_:Port,u:u64,v:u64|u==v,library(),programs(bank),a,z,actor,rule);
                mx::state_preservation(|_:Port,u:u64,v:u64|u==v,library(),programs(bank),a,z,actor,rule);
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
                    &&& z.current[n]==continuation(self.rows[n as int].blueprint,self.rows[n as int].current)
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

    /// Apply the actual receipt, retaining its captured provider. No current
    /// publication lookup occurs here.
    fn undo_one(&mut self,receipt:Receipt)->(out:Result<(),DriverError>)
        requires old(self).wf(),r::registered(old(self).control(),receipt.actor),
            old(self).control().fibers[receipt.actor].phase==Phase::Unloading,
        ensures final(self).wf(),final(self).rows@==old(self).rows@,final(self).blueprints@==old(self).blueprints@,
            out.is_ok() ==> mx::undo(receipt.model(),old(self).primitive_state()).is_some()
                && final(self).primitive_state()==mx::undo(receipt.model(),old(self).primitive_state()).unwrap(),
    {
        let ghost before=*self;
        let actor=receipt.actor;
        if !self.registered(actor) {return Err(DriverError::Unknown);}
        let result=match receipt.inverse {
            Inverse::Unit=>Ok(()),
            Inverse::Provision {key}=>{
                proof {self.table_declaration(actor,key);}
                let index=match self.tables[actor].locate(key) {Some(i)=>i,None=>return Err(DriverError::MissingBinding)};
                if self.tables[actor].slots[index].value.is_none() {return Err(DriverError::MissingValue);}
                self.write_slot(actor,index,None);Ok(())
            },
            Inverse::Xor {provider,key,mask}=>{
                let current=self.provider(actor,key)?;
                if current!=provider {return Err(DriverError::MissingBinding);}
                let index=match self.tables[provider].locate(key) {Some(i)=>i,None=>return Err(DriverError::MissingValue)};
                let value=match self.tables[provider].slots[index].value {Some(v)=>v,None=>return Err(DriverError::MissingValue)};
                self.write_slot(provider,index,Some(value^mask));Ok(())
            },
            Inverse::Child {child}=>match self.kernel.retire(child) {
                Err(e)=>Err(DriverError::Kernel(e)),
                Ok(())=>{
                    proof {
                        let expected=mx::undo(receipt.model(),before.primitive_state()).unwrap();
                        assert(r::frame(before.control(),self.control(),child));
                        assert(self.control().fibers.dom() =~= before.control().fibers.dom()) by {
                            assert forall|n:usize| self.control().fibers.dom().contains(n)==before.control().fibers.dom().contains(n) by {
                                if n!=child {assert(r::registered(self.control(),n)==r::registered(before.control(),n));}
                            }
                        }
                        assert(self.control().fibers[child]==expected.control.fibers[child]);
                        assert(self.control().fibers =~= expected.control.fibers) by {
                            assert forall|n:usize| self.control().fibers.dom().contains(n) implies self.control().fibers[n]==expected.control.fibers[n] by {
                                if n!=child {
                                    assert(r::registered(before.control(),n));
                                    assert(self.control().fibers[n]==before.control().fibers[n]);
                                }
                            }
                        }
                        assert(self.tables() =~= before.tables());
                    }
                    Ok(())
                },
            },
        };
        proof {
            if result.is_ok() {
                let expected=mx::undo(receipt.model(),before.primitive_state()).unwrap();
                assert(self.physical(expected));
                assert(self.primitive_state().effects =~= expected.effects);
                assert(self.primitive_state().iterators =~= expected.iterators);
                assert(self.primitive_state().accumulators =~= expected.accumulators);
            }
        }
        result
    }

    /// Restore the mixed journal from last to first, then discard commitment.
    /// Any error leaves the complete public state and journal unchanged.
    pub fn unload(&mut self,actor:usize)->(out:Result<(),DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_err() ==> final(self).observation()==old(self).observation() && final(self).same(old(self)),
            out.is_ok() ==> final(self).journal(actor).len()==0
                && final(self).control().fibers[actor].phase==Phase::Inactive && old(self).ack(final(self),actor,r::Rule::Unload),
    {
        let mut draft=self.duplicate();
        let ghost initial=draft;
        match draft.unload_inner(actor) {Err(e)=>Err(e),Ok(())=>{
            proof {draft.unload_simulation(&initial,actor);reveal(MixedDriver::ack);}
            *self=draft;Ok(())
        }}
    }

    #[verifier::spinoff_prover]
    proof fn unload_simulation(&self,initial:&Self,actor:usize)
        requires self.wf(),initial.wf(),
            r::registered(initial.control(),actor),initial.control().fibers[actor].phase==Phase::Unloading,!r::relied(initial.control(),actor),
            self.journal(actor).len()==0,self.rows[actor as int].current.is_none(),
            self.rows.len()==initial.rows.len(),self.blueprints@==initial.blueprints@,
            self.rows[actor as int].blueprint==initial.rows[actor as int].blueprint,
            forall|i:int| 0<=i<initial.rows.len() && i!=actor ==> self.rows[i]==initial.rows[i],
            restore_receipts(initial.journal(actor),initial.primitive_state()).is_some(),
            self.primitive_state()==s::edit(restore_receipts(initial.journal(actor),initial.primitive_state()).unwrap(),actor,Phase::Inactive,ISet::empty(),None,Seq::empty()),
        ensures initial.ack(self,actor,r::Rule::Unload),
    {
        reveal(MixedDriver::ack);library_theory();
        assert forall|bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>| initial.represents(bank,a) && mx::well_formed(library(),programs(bank),a)
            implies exists|z:mx::Configuration<u64,Index>| mx::step(library(),programs(bank),a,z,actor,r::Rule::Unload) && self.represents(bank,z) by {
            assert forall|i:int| #![trigger a.state.accumulators[actor][i]] 0<=i<a.state.accumulators[actor].len() implies {
                let token=a.state.accumulators[actor][i];token<a.history.len()
                    && a.history[token as int].landed.receipt==initial.journal(actor)[i].model() && initial.journal(actor)[i].actor==actor
            } by {assert(initial.rows[actor as int].journal[i].actor==actor);}
            restore_journal(a.history,a.state.accumulators[actor],initial.journal(actor),a.state,actor);
            restore_payload(initial.journal(actor),initial.primitive_state(),a.state);
            let restored=mx::restore(a.history,a.state.accumulators[actor],a.state,actor).unwrap();
            let z=mx::unload(a,actor);
            assert(mx::step(library(),programs(bank),a,z,actor,r::Rule::Unload));
            mx::restore_preservation(library(),programs(bank),a.history,a.state.accumulators[actor],a.state,actor);
            mx::state_preservation(|_:Port,x:u64,y:u64|x==y,library(),programs(bank),a,z,actor,r::Rule::Unload);
            assert(self.physical(z.state));
            assert forall|n:usize| r::registered(self.control(),n) implies {
                &&& n<self.rows.len()
                &&& z.roots[n]==(Index {blueprint:self.rows[n as int].blueprint,pc:0})
                &&& z.current[n]==continuation(self.rows[n as int].blueprint,self.rows[n as int].current)
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
    fn unload_inner(&mut self,actor:usize)->(out:Result<(),DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_ok() ==> {
            &&& final(self).journal(actor).len()==0 && final(self).rows[actor as int].current.is_none()
            &&& final(self).control().fibers[actor].phase==Phase::Inactive
            &&& r::registered(old(self).control(),actor) && old(self).control().fibers[actor].phase==Phase::Unloading
            &&& !r::relied(old(self).control(),actor)
            &&& final(self).rows.len()==old(self).rows.len() && final(self).blueprints@==old(self).blueprints@
            &&& final(self).rows[actor as int].blueprint==old(self).rows[actor as int].blueprint
            &&& forall|i:int| 0<=i<old(self).rows.len() && i!=actor ==> final(self).rows[i]==old(self).rows[i]
            &&& restore_receipts(old(self).journal(actor),old(self).primitive_state()).is_some()
            &&& final(self).primitive_state()==s::edit(restore_receipts(old(self).journal(actor),old(self).primitive_state()).unwrap(),
                actor,Phase::Inactive,ISet::empty(),None,Seq::empty())
        },
    {
        let ghost initial=*self;
        if !self.registered(actor) {return Err(DriverError::Unknown);}
        if let Err(e)=self.kernel.begin_cleanup(actor) {return Err(DriverError::Kernel(e));}
        proof {
            assert(Kernel::node_ok(self.kernel.nodes@,actor as int));
            assert(self.kernel.nodes[actor as int].phase==Phase::Unloading);
            self.kernel.paper_observations(actor);
            assert(!r::relied(self.control(),actor)) by {
                assert forall|n:usize,b:crate::Binding| r::registered(self.control(),n) && self.control().fibers[n].committed.contains(b)
                    implies b.provider!=actor by {
                    self.kernel.paper_observations(n);
                    assert(self.kernel.binding_recorded(n,b));
                }
            }
        }
        proof {self.canonical_equal(&initial);}
        while !self.rows[actor].journal.is_empty()
            invariant self.wf(),actor<self.rows.len(),r::registered(self.control(),actor),
                self.control().fibers[actor].phase==Phase::Unloading,
                r::registered(initial.control(),actor),initial.control().fibers[actor].phase==Phase::Unloading,!r::relied(initial.control(),actor),
                self.rows.len()==initial.rows.len(),self.blueprints@==initial.blueprints@,
                self.rows[actor as int].blueprint==initial.rows[actor as int].blueprint,
                forall|i:int| 0<=i<self.rows.len() && i!=actor ==> self.rows[i]==initial.rows[i],
                restore_receipts(initial.journal(actor),initial.primitive_state())==restore_receipts(self.journal(actor),self.primitive_state()),
            decreases self.rows[actor as int].journal.len(),
        {
            let ghost previous=*self;
            let index=self.rows[actor].journal.len()-1;
            let receipt=self.rows[actor].journal[index];
            self.undo_one(receipt)?;
            let ghost undone=*self;
            let ghost restored=self.primitive_state();
            let _removed=self.rows[actor].journal.pop();
            proof {
                assert(receipt==previous.journal(actor).last());
                assert(self.journal(actor)==previous.journal(actor).drop_last());
                assert forall|n:int,i:int| #![trigger self.rows[n].journal[i]] 0<=n<self.rows.len() && 0<=i<self.rows[n].journal.len()
                    implies self.rows[n].journal[i].actor==n by {
                    if n==actor {assert(self.rows[n].journal[i]==undone.rows[n].journal[i]);}
                    else {assert(self.rows[n]==undone.rows[n]);}
                }
                self.canonical_equal(&undone);
                assert(self.primitive_state()==restored);
                assert(restore_receipts(previous.journal(actor),previous.primitive_state())==restore_receipts(self.journal(actor),self.primitive_state()));
            }
        }
        let ghost restored=*self;
        if let Err(e)=self.kernel.finish_cleanup(actor) {return Err(DriverError::Kernel(e));}
        self.rows[actor].current=None;
        proof {
            self.kernel.paper_observations(actor);
            let expected=s::edit(restored.primitive_state(),actor,Phase::Inactive,ISet::empty(),None,Seq::empty());
            assert(self.control().fibers.dom() =~= expected.control.fibers.dom()) by {
                assert forall|n:usize| self.control().fibers.dom().contains(n)==expected.control.fibers.dom().contains(n) by {
                    if n!=actor {assert(r::registered(self.control(),n)==r::registered(restored.control(),n));}
                }
            }
            assert(self.control().fibers =~= expected.control.fibers) by {
                assert forall|n:usize| r::registered(self.control(),n) implies self.control().fibers[n]==expected.control.fibers[n] by {
                    if n!=actor {assert(self.control().fibers[n]==restored.control().fibers[n]);}
                }
            }
            assert(self.tables() =~= expected.tables);
            assert(self.primitive_state().effects =~= expected.effects);
            assert(self.primitive_state().iterators =~= expected.iterators);
            assert(self.primitive_state().accumulators =~= expected.accumulators);
        }
        Ok(())
    }

    fn table_empty(&self,id:usize)->(yes:bool)
        requires self.wf(),id<self.tables.len(),
        ensures yes==self.table(id).is_empty(),
    {
        let mut i=0;
        while i<self.tables[id].slots.len()
            invariant self.wf(),id<self.tables.len(),i<=self.tables[id as int].slots.len(),
                forall|j:int|0<=j<i ==> self.tables[id as int].slots[j].value.is_none(),
            decreases self.tables[id as int].slots.len()-i,
        {
            if self.tables[id].slots[i].value.is_some() {
                proof {
                    let key=self.tables[id as int].slots[i as int].key;
                    assert(self.tables[id as int].find(key)==Some(i));
                    assert(self.table(id).dom().contains(key));
                }
                return false;
            }
            i+=1;
        }
        assert(self.table(id).dom().is_empty());true
    }

    pub fn remove(&mut self,id:usize)->(out:Result<(),DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_err() ==> final(self).observation()==old(self).observation() && final(self).same(old(self)),
            out.is_ok() ==> r::step(old(self).control(),final(self).control(),id,r::Rule::Remove)
                && old(self).ack(final(self),id,r::Rule::Remove),
    {
        if !self.registered(id) {return Err(DriverError::Unknown);}
        if !self.table_empty(id) {return Err(DriverError::NonemptyTable);}
        let mut owner=0;
        while owner<self.rows.len()
            invariant owner<=self.rows.len(),self.wf(),*self==*old(self),self.table(id).is_empty(),
                forall|n:int,j:int| #![trigger self.rows[n].journal[j]] 0<=n<owner && 0<=j<self.rows[n].journal.len()
                    ==> self.rows[n].journal[j].inverse!=(Inverse::Child {child:id}),
            decreases self.rows.len()-owner,
        {
            let mut i=0;
            while i<self.rows[owner].journal.len()
                invariant owner<self.rows.len(),i<=self.rows[owner as int].journal.len(),self.wf(),*self==*old(self),
                    forall|j:int| 0<=j<i ==> self.rows[owner as int].journal[j].inverse!=(Inverse::Child {child:id}),
                decreases self.rows[owner as int].journal.len()-i,
            {
                if let Inverse::Child {child}=self.rows[owner].journal[i].inverse {
                    if child==id {return Err(DriverError::Retained);}
                }
                i+=1;
            }
            owner+=1;
        }
        let mut draft=self.duplicate();
        let ghost initial=draft;
        proof {assert(initial.unreferenced(id));}
        match draft.kernel.remove(id) {Err(e)=>Err(DriverError::Kernel(e)),Ok(())=>{
            proof {draft.administrative_simulation(&initial,id,r::Rule::Remove);reveal(MixedDriver::ack);}
            *self=draft;Ok(())
        }}
    }

    /// Dispatch through the same checked executable methods used individually.
    pub fn apply(&mut self,command:Command)->(out:Result<Transition,DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> out.unwrap().command()==command
                && old(self).ack(final(self),out.unwrap().label().0,out.unwrap().label().1),
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
    pub proof fn advance_source(&self,after:&Self,bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>,actor:usize,rule:r::Rule)->(z:mx::Configuration<u64,Index>)
        requires self.represents(bank,a),mx::well_formed(library(),programs(bank),a),self.ack(after,actor,rule),
        ensures mx::step(library(),programs(bank),a,z,actor,rule),after.represents(bank,z),mx::well_formed(library(),programs(bank),z),
    {
        reveal(MixedDriver::ack);library_theory();
        let z=choose|z:mx::Configuration<u64,Index>| mx::step(library(),programs(bank),a,z,actor,rule) && after.represents(bank,z);
        mx::configuration_preservation(|_:Port,x:u64,y:u64|x==y,library(),programs(bank),a,z,actor,rule);z
    }
    pub proof fn same_representation(&self,other:&Self,bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>)
        requires self.wf(),other.wf(),self.same(other),other.represents(bank,a),
        ensures self.represents(bank,a),
    {
        self.kernel.unchanged_observations(&other.kernel);
        assert(self.tables() =~= other.tables()) by {
            assert forall|n:usize| r::registered(self.control(),n) implies self.table(n)==other.table(n) by {
                self.kernel.paper_observations(n);self.row_bounds(n);other.row_bounds(n);
                self.tables[n as int].same_map(&other.tables[n as int]);
            }
        }
        assert(bank_same(self.blueprints@,bank)) by {
            assert forall|i:int|0<=i<self.blueprints.len() implies self.blueprints[i].same(&bank[i]) by {
                assert(self.blueprints[i].same(&other.blueprints[i]));assert(other.blueprints[i].same(&bank[i]));
            }
        }
    }
    pub fn phase(&self,id:usize)->(out:Option<Phase>)
        ensures out==if r::registered(self.control(),id) {Some(self.control().fibers[id].phase)} else {None},
    {proof {self.kernel.paper_observations(id);}self.kernel.phase(id)}
    pub fn retired(&self,id:usize)->bool {self.kernel.retired(id)}
    pub fn read(&self,id:usize,key:Port)->(out:Option<u64>)
        requires self.wf(),
        ensures r::registered(self.control(),id) ==> out==if self.table(id).dom().contains(key) {Some(self.table(id)[key])} else {None},
    {if !self.registered(id) {None} else {self.tables[id].read(key)}}
    pub fn inverse_count(&self,id:usize)->(out:Option<usize>)
        requires self.wf(),
        ensures r::registered(self.control(),id) ==> out.is_some() && out.unwrap()==self.journal(id).len(),
    {if !self.registered(id) {None} else {Some(self.rows[id].journal.len())}}
}

/// An executable caller collects these acknowledged successful method results.
/// Failed calls preserve the complete machine and may be omitted as stutters.
pub open spec fn acknowledged(machines:Seq<MixedDriver>,labels:Seq<(usize,r::Rule)>)->bool {
    machines.len()==labels.len()+1 && forall|i:int|0<=i<labels.len()
        ==> machines[i].ack(&machines[i+1],labels[i].0,labels[i].1)
}

/// Construct a single real mixed-grammar history from the executable contracts.
/// No source trace, fabricated journal equality, or supplied local Model is required.
#[verifier::spinoff_prover]
#[verifier::rlimit(20)]
pub proof fn execution_refines(bank:Seq<Blueprint>,machines:Seq<MixedDriver>,labels:Seq<(usize,r::Rule)>)
    requires acknowledged(machines,labels),machines.first().represents(bank,mx::empty()),
    ensures exists|states:Seq<mx::Configuration<u64,Index>>| {
        &&& mx::execution(library(),programs(bank),states,labels) && states.first()==mx::empty::<u64,Index>()
        &&& forall|i:int|0<=i<states.len() ==> machines[i].represents(bank,states[i])
    },
    decreases labels.len(),
{
    library_theory();
    if labels.len()==0 {
        let states=seq![mx::empty::<u64,Index>()];
        mx::empty_well_formed(library(),programs(bank));
        mx::from_empty_safe(|_:Port,x:u64,y:u64|x==y,library(),programs(bank),states,labels);
        assert forall|i:int|0<=i<states.len() implies machines[i].represents(bank,states[i]) by {
            assert(i==0);
            assert(machines[i]==machines.first());
            assert(states[i]==mx::empty::<u64,Index>());
        }
        assert(mx::execution(library(),programs(bank),states,labels));
        assert(states.first()==mx::empty::<u64,Index>());
        assert(exists|states:Seq<mx::Configuration<u64,Index>>| {
            &&& mx::execution(library(),programs(bank),states,labels) && states.first()==mx::empty::<u64,Index>()
            &&& forall|i:int|0<=i<states.len() ==> machines[i].represents(bank,states[i])
        });
    } else {
        let previous=machines.drop_last();let prefix=labels.drop_last();
        execution_refines(bank,previous,prefix);
        let states=choose|states:Seq<mx::Configuration<u64,Index>>| {
            &&& mx::execution(library(),programs(bank),states,prefix) && states.first()==mx::empty::<u64,Index>()
            &&& forall|i:int|0<=i<states.len() ==> previous[i].represents(bank,states[i])
        };
        mx::from_empty_safe(|_:Port,x:u64,y:u64|x==y,library(),programs(bank),states,prefix);
        let a=states.last();let actor=labels.last().0;let rule=labels.last().1;
        assert(previous.last().represents(bank,a));assert(mx::well_formed(library(),programs(bank),a));
        assert(previous.last().ack(&machines.last(),actor,rule));reveal(MixedDriver::ack);
        let z=choose|z:mx::Configuration<u64,Index>| mx::step(library(),programs(bank),a,z,actor,rule) && machines.last().represents(bank,z);
        mx::configuration_preservation(|_:Port,x:u64,y:u64|x==y,library(),programs(bank),a,z,actor,rule);
        let full=states.push(z);
        assert(mx::execution(library(),programs(bank),full,labels)) by {
            assert forall|i:int|0<=i<labels.len() implies mx::step(library(),programs(bank),full[i],full[i+1],labels[i].0,labels[i].1) by {
                if i<prefix.len() {
                    assert(full[i]==states[i] && full[i+1]==states[i+1]);assert(labels[i]==prefix[i]);
                    assert(mx::step(library(),programs(bank),states[i],states[i+1],prefix[i].0,prefix[i].1));
                } else {
                    assert(i==prefix.len());assert(full[i]==a && full[i+1]==z);assert(labels[i]==labels.last());
                }
            }
        }
        mx::from_empty_safe(|_:Port,x:u64,y:u64|x==y,library(),programs(bank),full,labels);
        assert forall|i:int|0<=i<full.len() implies machines[i].represents(bank,full[i])
            && mx::well_formed(library(),programs(bank),full[i]) && crate::preservation::resource_safe(full[i].state) by {
            if i<states.len() {assert(machines[i]==previous[i]);} else {assert(i==full.len()-1);}
        }
        assert(full.first()==mx::empty::<u64,Index>());
        assert(forall|i:int|0<=i<full.len() ==> machines[i].represents(bank,full[i]));
        assert(exists|states:Seq<mx::Configuration<u64,Index>>| {
            &&& mx::execution(library(),programs(bank),states,labels) && states.first()==mx::empty::<u64,Index>()
            &&& forall|i:int|0<=i<states.len() ==> machines[i].represents(bank,states[i])
        });
    }
}

/// Results of a finite, synchronous script. The first failure stops execution;
/// the successful prefix and its actual machine remain available to the caller.
pub struct ScriptReport {pub machine:MixedDriver,pub transitions:Vec<Transition>,pub error:Option<DriverError>}
impl ScriptReport {
    pub closed spec fn refines(&self,bank:Seq<Blueprint>)->bool {
        exists|states:Seq<mx::Configuration<u64,Index>>| {
            &&& mx::execution(library(),programs(bank),states,labels(self.transitions@)) && states.first()==mx::empty::<u64,Index>()
            &&& self.machine.represents(bank,states.last())
            &&& forall|i:int|0<=i<states.len() ==> mx::well_formed(library(),programs(bank),states[i]) && crate::preservation::resource_safe(states[i].state)
        }
    }
    proof fn establish(&self,bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>)
        requires mx::execution(library(),programs(bank),states,labels(self.transitions@)),states.first()==mx::empty::<u64,Index>(),
            self.machine.represents(bank,states.last()),
        ensures self.refines(bank),
    {library_theory();mx::from_empty_safe(|_:Port,x:u64,y:u64|x==y,library(),programs(bank),states,labels(self.transitions@));}
}

/// Actual execution, including the first strict failure. Its correspondence
/// starts from new/empty and has no caller-supplied model or history premise.
#[verifier::spinoff_prover]
pub fn run_script(blueprints:Vec<Blueprint>,commands:&[Command])->(out:ScriptReport)
    ensures out.machine.wf(),out.refines(blueprints@),out.transitions.len()<=commands.len(),
        out.error.is_none() ==> out.transitions.len()==commands.len(),
        out.error.is_some() ==> out.transitions.len()<commands.len(),
        forall|i:int|0<=i<out.transitions.len() ==> out.transitions[i].command()==commands[i],
{
    let ghost bank=blueprints@;
    let mut machine=MixedDriver::new(blueprints);let mut transitions:Vec<Transition>=Vec::new();let mut i=0;
    let ghost mut states=seq![mx::empty::<u64,Index>()];
    proof {mx::empty_well_formed(library(),programs(bank));}
    while i<commands.len()
        invariant i<=commands.len(),transitions.len()==i,machine.wf(),bank==blueprints@,
            forall|j:int|0<=j<i ==> transitions[j].command()==commands[j],
            states.first()==mx::empty::<u64,Index>(),mx::execution(library(),programs(bank),states,labels(transitions@)),
            machine.represents(bank,states.last()),mx::well_formed(library(),programs(bank),states.last()),
        decreases commands.len()-i,
    {
        let ghost before=machine;
        match machine.apply(commands[i]) {
            Err(error)=>{
                proof {machine.same_representation(&before,bank,states.last());}
                let out=ScriptReport {machine,transitions,error:Some(error)};
                proof {out.establish(bank,states);}return out;
            },
            Ok(transition)=>{
                let ghost previous=transitions@;
                transitions.push(transition);
                proof {
                    let z=before.advance_source(&machine,bank,states.last(),transition.label().0,transition.label().1);
                    let full=states.push(z);
                    assert(labels(transitions@)==labels(previous).push(transition.label()));
                    append_source(bank,states,labels(previous),z,transition.label());
                    states=full;
                }
                i+=1;
            },
        }
    }
    let out=ScriptReport {machine,transitions,error:None};
    proof {out.establish(bank,states);}out
}

proof fn append_source(bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>,prefix:Seq<(usize,r::Rule)>,z:mx::Configuration<u64,Index>,label:(usize,r::Rule))
    requires mx::execution(library(),programs(bank),states,prefix),mx::step(library(),programs(bank),states.last(),z,label.0,label.1),
    ensures mx::execution(library(),programs(bank),states.push(z),prefix.push(label)),
{
    assert forall|i:int|0<=i<prefix.len()+1 implies mx::step(library(),programs(bank),states.push(z)[i],states.push(z)[i+1],prefix.push(label)[i].0,prefix.push(label)[i].1) by {
        if i<prefix.len() {assert(mx::step(library(),programs(bank),states[i],states[i+1],prefix[i].0,prefix[i].1));}
        else {assert(i==prefix.len());assert(states.push(z)[i]==states.last());}
    }
}

}

#[path = "fresh_driver.rs"]
pub mod fresh;
