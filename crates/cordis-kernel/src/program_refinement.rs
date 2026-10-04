//! Value-carrying simulation of the fixed private-provision interpreter.
//!
//! Ports are the driver's checked immutable cell layout. Only written cells
//! appear in tables; the executable finish gate requires total publication.
//! The model interprets the same code and restores its actual stage-indexed
//! prefixes. Admission and the terminal poll are administrative stutters;
//! landing plus departure is one L-Divert when an admitted target has drifted.
#[cfg(verus_keep_ghost)]
use crate::program;
use crate::program::Instruction;
use crate::refinement as c;
use crate::resources::Cell;
#[cfg(verus_keep_ghost)]
use crate::semantics as s;
#[cfg(verus_keep_ghost)]
use crate::Phase;
use crate::Port;
use vstd::prelude::*;

verus! {
pub struct Snapshot {
    pub allocated:nat,
    pub control:c::State,
    pub layouts:IMap<usize,Seq<Port>>,
    pub codes:IMap<usize,Seq<Instruction>>,
    pub initial:IMap<usize,Seq<Cell>>,
    pub cells:IMap<usize,Seq<Cell>>,
    pub owners:IMap<usize,u64>,
    pub positions:IMap<usize,nat>,
    pub depths:IMap<usize,nat>,
    pub ended:IMap<usize,bool>,
}

pub open spec fn row_wf(x:Snapshot,n:usize) -> bool {
    &&& x.layouts[n].len() == x.cells[n].len() && x.cells[n].len() == x.initial[n].len()
    &&& x.codes[n].len() <= usize::MAX
    &&& x.depths[n] <= x.positions[n] <= x.codes[n].len()
    &&& (x.depths[n] > 0 ==> program::prefix(x.codes[n],x.owners[n],x.initial[n],(x.depths[n]-1) as nat).next < x.codes[n].len())
    &&& x.cells[n] == program::prefix(x.codes[n],x.owners[n],x.initial[n],x.depths[n]).cells
    &&& x.positions[n] == program::prefix(x.codes[n],x.owners[n],x.initial[n],x.depths[n]).next
    &&& forall|i:int| 0 <= i < x.codes[n].len() ==> x.codes[n][i].valid(i as usize,x.codes[n].len() as usize,x.cells[n].len())
    &&& forall|i:int,j:int| 0 <= i < x.layouts[n].len() && 0 <= j < x.layouts[n].len()
        && x.layouts[n][i] == x.layouts[n][j] ==> i == j
    &&& x.control.fibers[n].provisions == ISet::new(|p:Port| x.layouts[n].contains(p))
    &&& forall|i:int| 0 <= i < x.initial[n].len() ==> x.initial[n][i].depth == 0 && x.initial[n][i].owner.is_none()
    &&& forall|i:int| 0 <= i < x.cells[n].len() ==> x.cells[n][i].depth <= x.depths[n]
        && (x.cells[n][i].depth == 0 ==> x.cells[n][i] == x.initial[n][i])
    &&& (x.control.fibers[n].phase == Phase::Inactive ==> x.depths[n] == 0)
    &&& (x.control.fibers[n].phase == Phase::Active ==> x.ended[n]
        && forall|i:int| 0 <= i < x.cells[n].len() ==> x.cells[n][i].depth > 0)
    &&& (x.ended[n] ==> x.positions[n] == x.codes[n].len())
}

pub open spec fn wf(x:Snapshot) -> bool {
    &&& c::well_formed(x.control)
    &&& forall|n:usize| c::registered(x.control,n) ==> n < x.allocated
    &&& x.layouts.dom() == x.control.fibers.dom() && x.codes.dom() == x.control.fibers.dom()
    &&& x.initial.dom() == x.control.fibers.dom() && x.cells.dom() == x.control.fibers.dom()
    &&& x.owners.dom() == x.control.fibers.dom() && x.positions.dom() == x.control.fibers.dom()
    &&& x.depths.dom() == x.control.fibers.dom() && x.ended.dom() == x.control.fibers.dom()
    &&& forall|n:usize| c::registered(x.control,n) ==> row_wf(x,n)
}

pub open spec fn table(layout:Seq<Port>,cells:Seq<Cell>) -> IMap<Port,Cell> {
    IMap::new(|p:Port| exists|i:int| 0 <= i < layout.len() && layout[i] == p && cells[i].depth > 0,
        |p:Port| cells[choose|i:int| 0 <= i < layout.len() && layout[i] == p && cells[i].depth > 0])
}

pub open spec fn decode(layout:Seq<Port>,initial:Seq<Cell>,bindings:IMap<Port,Cell>) -> Seq<Cell> {
    Seq::new(layout.len(),|i:int| if bindings.dom().contains(layout[i]) {bindings[layout[i]]} else {initial[i]})
}

pub proof fn decode_table(layout:Seq<Port>,initial:Seq<Cell>,cells:Seq<Cell>)
    requires layout.len() == cells.len(),cells.len() == initial.len(),
        forall|i:int,j:int| 0 <= i < layout.len() && 0 <= j < layout.len() && layout[i] == layout[j] ==> i == j,
        forall|i:int| 0 <= i < cells.len() && cells[i].depth == 0 ==> cells[i] == initial[i],
    ensures decode(layout,initial,table(layout,cells)) == cells,
{
    let bindings = table(layout,cells);
    assert(decode(layout,initial,bindings) =~= cells) by {
        assert forall|i:int| 0 <= i < cells.len() implies decode(layout,initial,bindings)[i] == cells[i] by {
            if cells[i].depth > 0 {
                assert(bindings.dom().contains(layout[i]));
                let j = choose|j:int| 0 <= j < layout.len() && layout[j] == layout[i] && cells[j].depth > 0;
                assert(j == i);
            } else if bindings.dom().contains(layout[i]) {
                let j = choose|j:int| 0 <= j < layout.len() && layout[j] == layout[i] && cells[j].depth > 0;
                assert(j == i);
            }
        }
    }
}

pub open spec fn base() -> nat { 18446744073709551616nat }
pub open spec fn token(actor:usize,stage:nat) -> nat { actor as nat * base() + stage }
pub open spec fn token_actor(id:nat) -> usize { (id / base()) as usize }
pub open spec fn token_stage(id:nat) -> nat { id % base() }
pub proof fn token_round_trip(actor:usize,stage:nat)
    requires stage < base(),
    ensures token_actor(token(actor,stage)) == actor,token_stage(token(actor,stage)) == stage,
{
    assert((actor as nat * base() + stage) / base() == actor as nat) by(nonlinear_arith)
        requires stage < base(),base() > 0;
    assert((actor as nat * base() + stage) % base() == stage) by(nonlinear_arith)
        requires stage < base(),base() > 0;
}

pub open spec fn tokens(actor:usize,length:nat) -> Seq<nat> { Seq::new(length,|i:int| token(actor,i as nat)) }
pub open spec fn extra_terminal(x:Snapshot,n:usize) -> bool {
    x.ended[n] && (x.control.fibers[n].phase == Phase::Active || x.control.fibers[n].phase == Phase::Unloading)
}

pub open spec fn project(x:Snapshot) -> s::State<Cell> {
    s::State {
        control:x.control,
        tables:IMap::new(|n:usize| c::registered(x.control,n),|n:usize| table(x.layouts[n],x.cells[n])),
        effects:IMap::new(|n:usize| c::registered(x.control,n),|n:usize| 0nat),
        iterators:IMap::new(|n:usize| c::registered(x.control,n),|n:usize|
            if x.control.fibers[n].phase == Phase::Loading {Some(x.positions[n])} else {None}),
        accumulators:IMap::new(|n:usize| c::registered(x.control,n),|n:usize|
            tokens(n,x.depths[n] + if extra_terminal(x,n) {1nat} else {0nat})),
    }
}

pub open spec fn with_table(a:s::State<Cell>,n:usize,t:IMap<Port,Cell>) -> s::State<Cell> {
    s::State{control:a.control,tables:a.tables.insert(n,t),effects:a.effects,iterators:a.iterators,accumulators:a.accumulators}
}

/// Configuration is fixed code, ownership, cell layout and initial context.
/// No caller-supplied callback or asserted callback post-state occurs here.
pub open spec fn model(configuration:Snapshot) -> s::Model<Cell> {
    s::Model {
        iterate:|actor:usize,pc:nat,a:s::State<Cell>| {
            let depth = a.accumulators[actor].len();
            if pc < configuration.codes[actor].len() {
                let cells = decode(configuration.layouts[actor],configuration.initial[actor],a.tables[actor]);
                let result = program::interpret(configuration.codes[actor],pc as usize,configuration.owners[actor],cells);
                s::Yield{state:with_table(a,actor,table(configuration.layouts[actor],result.cells)),
                    inverse:token(actor,depth),next:Some(result.next as nat)}
            } else {
                s::Yield{state:a,inverse:token(actor,depth),next:None}
            }
        },
        undo:|id:nat,a:s::State<Cell>| {
            let actor = token_actor(id);
            let stage = token_stage(id);
            let before = program::prefix(configuration.codes[actor],configuration.owners[actor],configuration.initial[actor],stage);
            with_table(a,actor,table(configuration.layouts[actor],before.cells))
        },
    }
}

/// Fixed configuration and the actual fields preserved outside one actor.
pub open spec fn row_frame(a:Snapshot,z:Snapshot,n:usize) -> bool {
    &&& a.control.fibers.dom() == z.control.fibers.dom()
    &&& a.allocated == z.allocated
    &&& forall|m:usize| c::registered(a.control,m) ==> {
        &&& a.layouts[m] == z.layouts[m] && a.codes[m] == z.codes[m]
        &&& a.initial[m] == z.initial[m] && a.owners[m] == z.owners[m]
        &&& (m != n ==> a.cells[m] == z.cells[m] && a.positions[m] == z.positions[m]
            && a.depths[m] == z.depths[m] && a.ended[m] == z.ended[m])
    }
}

/// This relation records the executed instruction's concrete payload, before
/// control acknowledges a possible diversion. It assumes no paper step.
pub open spec fn landed(a:Snapshot,z:Snapshot,n:usize) -> bool {
    let expected = program::interpret(a.codes[n],a.positions[n] as usize,a.owners[n],a.cells[n]);
    &&& row_frame(a,z,n) && a.control == z.control
    &&& c::registered(a.control,n) && a.control.fibers[n].phase == Phase::Loading
    &&& a.positions[n] < a.codes[n].len() && !a.ended[n] && !z.ended[n]
    &&& z.cells[n] == expected.cells && z.positions[n] == expected.next
    &&& z.depths[n] == a.depths[n]+1
}

pub proof fn table_domain(layout:Seq<Port>,cells:Seq<Cell>)
    requires layout.len() == cells.len(),
    ensures table(layout,cells).dom().subset_of(ISet::new(|p:Port| layout.contains(p))),
        (forall|i:int| 0 <= i < cells.len() ==> cells[i].depth > 0)
            ==> table(layout,cells).dom() == ISet::new(|p:Port| layout.contains(p)),
        (forall|i:int| 0 <= i < cells.len() ==> cells[i].depth == 0) ==> table(layout,cells).is_empty(),
{
    let t = table(layout,cells);
    assert forall|p:Port| t.dom().contains(p) implies layout.contains(p) by {
        let i = choose|i:int| 0 <= i < layout.len() && layout[i] == p && cells[i].depth > 0;
    }
    if forall|i:int| 0 <= i < cells.len() ==> cells[i].depth > 0 {
        assert(t.dom() =~= ISet::new(|p:Port| layout.contains(p))) by {
            assert forall|p:Port| layout.contains(p) implies t.dom().contains(p) by {
                let i = choose|i:int| 0 <= i < layout.len() && layout[i] == p;
                assert(cells[i].depth > 0);
            }
        }
    }
}

pub proof fn projection_well_formed(x:Snapshot)
    requires wf(x),
    ensures crate::preservation::well_formed(project(x)),s::total_active(project(x)),
{
    let a = project(x);
    assert(a.tables.dom() =~= x.control.fibers.dom());
    assert(a.effects.dom() =~= x.control.fibers.dom());
    assert(a.iterators.dom() =~= x.control.fibers.dom());
    assert(a.accumulators.dom() =~= x.control.fibers.dom());
    assert forall|n:usize| c::registered(x.control,n) implies {
        &&& a.tables[n].dom().subset_of(a.control.fibers[n].provisions)
        &&& (a.control.fibers[n].phase == Phase::Inactive ==> a.iterators[n].is_none()
            && a.accumulators[n].len() == 0 && a.control.fibers[n].committed.is_empty())
        &&& (a.control.fibers[n].phase == Phase::Loading ==> a.iterators[n].is_some())
        &&& (a.control.fibers[n].phase == Phase::Active || a.control.fibers[n].phase == Phase::Unloading ==> a.iterators[n].is_none())
    } by {
        assert(row_wf(x,n));
        table_domain(x.layouts[n],x.cells[n]);
        if a.control.fibers[n].phase == Phase::Inactive {
            assert forall|b:crate::Binding| a.control.fibers[n].committed.contains(b) implies false by { }
        }
    }
    assert forall|n:usize| s::registered(a,n) && a.control.fibers[n].phase == Phase::Active
        implies a.tables[n].dom() == a.control.fibers[n].provisions by {
        assert(row_wf(x,n));table_domain(x.layouts[n],x.cells[n]);
    }
}

pub proof fn tokens_push(actor:usize,length:nat)
    ensures tokens(actor,length+1) == tokens(actor,length).push(token(actor,length)),
{
    assert(tokens(actor,length+1) =~= tokens(actor,length).push(token(actor,length)));
}

/// The ordinary coherent landing is L-Iter of the fixed instruction model. This
/// theorem consumes the actual driver landing relation, not an arbitrary map.
pub proof fn landed_iter(a:Snapshot,z:Snapshot,n:usize)
    requires wf(a),wf(z),landed(a,z,n),c::coherent(a.control,n),
    ensures s::step(model(a),project(a),project(z),n,c::Rule::Iter),
{
    projection_well_formed(a);
    s::total_targets_agree(project(a),n,a.control.fibers[n].committed);
    assert(row_wf(a,n));
    decode_table(a.layouts[n],a.initial[n],a.cells[n]);
    let x = project(a);
    let y = (model(a).iterate)(n,a.positions[n],x);
    tokens_push(n,a.depths[n]);
    let expected = s::edit(y.state,n,Phase::Loading,a.control.fibers[n].committed,y.next,x.accumulators[n].push(y.inverse));
    assert(expected.control == z.control) by {
        assert(expected.control.fibers =~= z.control.fibers);
    }
    assert(expected.tables =~= project(z).tables) by {
        assert forall|m:usize| c::registered(z.control,m) implies expected.tables[m] == project(z).tables[m] by {
            if m != n { assert(a.cells[m] == z.cells[m]); }
        }
    }
    assert(expected.effects =~= project(z).effects);
    assert(expected.iterators =~= project(z).iterators) by {
        assert forall|m:usize| c::registered(z.control,m) implies expected.iterators[m] == project(z).iterators[m] by {
            if m != n { assert(a.positions[m] == z.positions[m]); }
        }
    }
    assert(expected.accumulators =~= project(z).accumulators) by {
        assert forall|m:usize| c::registered(z.control,m) implies expected.accumulators[m] == project(z).accumulators[m] by {
            if m != n { assert(a.depths[m] == z.depths[m] && a.ended[m] == z.ended[m]); }
        }
    }
    assert(expected == project(z));
}

/// Every encoded cleanup token resets precisely its owner's witnessed program
/// prefix. Other providers' table contents and every control field are framed.
pub proof fn undo_program_prefix(configuration:Snapshot,a:s::State<Cell>,actor:usize,stage:nat)
    requires stage < base(),s::registered(a,actor),
    ensures (model(configuration).undo)(token(actor,stage),a) == with_table(a,actor,
        table(configuration.layouts[actor],program::prefix(configuration.codes[actor],configuration.owners[actor],configuration.initial[actor],stage).cells)),
    {
        let z = (model(configuration).undo)(token(actor,stage),a);
        &&& z.control == a.control && z.effects == a.effects && z.iterators == a.iterators && z.accumulators == a.accumulators
        &&& z.tables[actor] == table(configuration.layouts[actor],program::prefix(configuration.codes[actor],configuration.owners[actor],configuration.initial[actor],stage).cells)
        &&& forall|n:usize| n != actor ==> z.tables[n] == a.tables[n]
    },
{ token_round_trip(actor,stage); }

pub proof fn restore_program(configuration:Snapshot,a:s::State<Cell>,actor:usize,length:nat)
    requires wf(configuration),c::registered(configuration.control,actor),s::registered(a,actor),length > 0,length <= base(),
    ensures s::restore(model(configuration),tokens(actor,length),a)
        == with_table(a,actor,table(configuration.layouts[actor],configuration.initial[actor])),
    decreases length,
{
    reveal_with_fuel(s::restore,2);
    let last = token(actor,(length-1) as nat);
    assert(tokens(actor,length).last() == last);
    assert(tokens(actor,length).drop_last() =~= tokens(actor,(length-1) as nat));
    undo_program_prefix(configuration,a,actor,(length-1) as nat);
    let middle = (model(configuration).undo)(last,a);
    if length > 1 {
        restore_program(configuration,middle,actor,(length-1) as nat);
        assert(with_table(middle,actor,table(configuration.layouts[actor],configuration.initial[actor]))
            == with_table(a,actor,table(configuration.layouts[actor],configuration.initial[actor]))) by {
            assert(middle.tables.insert(actor,table(configuration.layouts[actor],configuration.initial[actor]))
                =~= a.tables.insert(actor,table(configuration.layouts[actor],configuration.initial[actor])));
        }
    }
}

pub proof fn domain_preserved(a:c::State,z:c::State,n:usize)
    requires c::registered(a,n),c::registered(z,n),c::frame(a,z,n),
    ensures a.fibers.dom() == z.fibers.dom(),
{
    assert(a.fibers.dom() =~= z.fibers.dom()) by {
        assert forall|m:usize| a.fibers.dom().contains(m) == z.fibers.dom().contains(m) by {
            if m != n { assert(c::registered(a,m) == c::registered(z,m)); }
        }
    }
}

pub proof fn projection_local_edit(a:Snapshot,z:Snapshot,n:usize)
    requires wf(a),wf(z),row_frame(a,z,n),c::registered(a.control,n),c::registered(z.control,n),
        c::frame(a.control,z.control,n),c::interface_same(a.control.fibers[n],z.control.fibers[n]),
        a.control.fibers[n].retired == z.control.fibers[n].retired,
    ensures project(z) == s::edit(with_table(project(a),n,table(z.layouts[n],z.cells[n])),n,
        z.control.fibers[n].phase,z.control.fibers[n].committed,
        project(z).iterators[n],project(z).accumulators[n]),
{
    let x = s::edit(with_table(project(a),n,table(z.layouts[n],z.cells[n])),n,
        z.control.fibers[n].phase,z.control.fibers[n].committed,project(z).iterators[n],project(z).accumulators[n]);
    assert(x.control.fibers =~= z.control.fibers) by {
        assert(x.control.fibers.dom() =~= z.control.fibers.dom());
        assert forall|m:usize| x.control.fibers.dom().contains(m) implies x.control.fibers[m] == z.control.fibers[m] by {
            assert(c::registered(z.control,m));
            if m != n { assert(a.control.fibers[m] == z.control.fibers[m]); }
        }
    }
    assert(x.tables =~= project(z).tables) by {
        assert forall|m:usize| c::registered(z.control,m) implies x.tables[m] == project(z).tables[m] by {
            if m != n { assert(a.cells[m] == z.cells[m]); }
        }
    }
    assert(x.effects =~= project(z).effects);
    assert(x.iterators =~= project(z).iterators) by {
        assert forall|m:usize| c::registered(z.control,m) implies x.iterators[m] == project(z).iterators[m] by {
            if m != n { assert(a.positions[m] == z.positions[m]); assert(a.control.fibers[m] == z.control.fibers[m]); }
        }
    }
    assert(x.accumulators =~= project(z).accumulators) by {
        assert forall|m:usize| c::registered(z.control,m) implies x.accumulators[m] == project(z).accumulators[m] by {
            if m != n { assert(a.depths[m] == z.depths[m] && a.ended[m] == z.ended[m]); assert(a.control.fibers[m] == z.control.fibers[m]); }
        }
    }
}

pub proof fn table_reinsert(a:s::State<Cell>,n:usize)
    requires a.tables.dom().contains(n),
    ensures with_table(a,n,a.tables[n]) == a,
{ assert(a.tables.insert(n,a.tables[n]) =~= a.tables); }

pub open spec fn finish_ack(a:Snapshot,z:Snapshot,n:usize) -> bool {
    row_frame(a,z,n) && c::step(a.control,z.control,n,c::Rule::Finish)
        && a.cells[n] == z.cells[n] && a.positions[n] == z.positions[n] && a.depths[n] == z.depths[n]
        && a.ended[n] && z.ended[n]
}

/// The terminal poll changes only private metadata. Its control acknowledgement
/// is L-Finish, adding the identity inverse of the actual terminal continuation.
pub proof fn finished(a:Snapshot,z:Snapshot,n:usize)
    requires wf(a),wf(z),finish_ack(a,z,n),
    ensures s::step(model(a),project(a),project(z),n,c::Rule::Finish),
{
    assert(row_wf(a,n));
    projection_well_formed(a);
    projection_local_edit(a,z,n);
    table_reinsert(project(a),n);
    s::total_targets_agree(project(a),n,a.control.fibers[n].committed);
    tokens_push(n,a.depths[n]);
}

pub open spec fn unload_ack(a:Snapshot,z:Snapshot,n:usize) -> bool {
    row_frame(a,z,n) && c::step(a.control,z.control,n,c::Rule::Unload)
        && z.cells[n] == a.initial[n] && z.depths[n] == 0 && z.positions[n] == 0 && !z.ended[n]
}

/// The actual guarded bulk recovery agrees with the complete abstract inverse
/// accumulator, including a terminal identity token when one was acknowledged.
pub proof fn unloaded(a:Snapshot,z:Snapshot,n:usize)
    requires wf(a),wf(z),unload_ack(a,z,n),
    ensures s::step(model(a),project(a),project(z),n,c::Rule::Unload),
{
    assert(row_wf(a,n));
    assert(row_wf(z,n));
    projection_local_edit(a,z,n);
    let length = a.depths[n]+if extra_terminal(a,n) {1nat} else {0nat};
    if length > 0 {
        restore_program(a,project(a),n,length);
    } else {
        assert(a.depths[n] == 0);
        assert(a.cells[n] == a.initial[n]);
        projection_well_formed(a);
        table_reinsert(project(a),n);
    }
    assert(tokens(n,0) =~= Seq::<nat>::empty());
    assert(z.control.fibers[n].committed =~= ISet::<crate::Binding>::empty());
    assert(project(z) == s::edit(s::restore(model(a),project(a).accumulators[n],project(a)),n,Phase::Inactive,ISet::empty(),None,Seq::empty()));
}

pub open spec fn depart_ack(a:Snapshot,z:Snapshot,n:usize) -> bool {
    row_frame(a,z,n)
        && c::step(a.control,z.control,n,if a.control.fibers[n].phase == Phase::Loading {c::Rule::Divert} else {c::Rule::Leave})
        && a.cells[n] == z.cells[n] && a.positions[n] == z.positions[n] && a.depths[n] == z.depths[n]
        && a.ended[n] == z.ended[n]
}

/// If terminal polling already ended the private program, diversion lands its
/// identity result. Otherwise departure uses the no-iteration Divert arm.
pub proof fn departed(a:Snapshot,z:Snapshot,n:usize)
    requires wf(a),wf(z),depart_ack(a,z,n),
    ensures s::step(model(a),project(a),project(z),n,
        if a.control.fibers[n].phase == Phase::Loading {c::Rule::Divert} else {c::Rule::Leave}),
{
    assert(row_wf(a,n));
    projection_well_formed(a);
    s::total_targets_agree(project(a),n,a.control.fibers[n].committed);
    projection_local_edit(a,z,n);
    table_reinsert(project(a),n);
    if a.control.fibers[n].phase == Phase::Loading && a.ended[n] { tokens_push(n,a.depths[n]); }
}

/// A write admitted before target drift lands before departure. Composing the
/// two real method relations is the atomic second arm of L-Divert.
pub proof fn landed_divert(a:Snapshot,landed_state:Snapshot,z:Snapshot,n:usize)
    requires wf(a),wf(landed_state),wf(z),landed(a,landed_state,n),depart_ack(landed_state,z,n),
    ensures s::step(model(a),project(a),project(z),n,c::Rule::Divert),
{
    assert(row_wf(a,n));
    projection_well_formed(a);
    s::total_targets_agree(project(a),n,a.control.fibers[n].committed);
    decode_table(a.layouts[n],a.initial[n],a.cells[n]);
    assert(row_frame(a,z,n)) by {
        assert forall|m:usize| c::registered(a.control,m) implies {
            &&& a.layouts[m] == z.layouts[m] && a.codes[m] == z.codes[m]
            &&& a.initial[m] == z.initial[m] && a.owners[m] == z.owners[m]
            &&& (m != n ==> a.cells[m] == z.cells[m] && a.positions[m] == z.positions[m]
                && a.depths[m] == z.depths[m] && a.ended[m] == z.ended[m])
        } by { assert(c::registered(landed_state.control,m)); }
    }
    projection_local_edit(a,z,n);
    tokens_push(n,a.depths[n]);
}

pub open spec fn begin_ack(a:Snapshot,z:Snapshot,n:usize) -> bool {
    row_frame(a,z,n) && c::step(a.control,z.control,n,c::Rule::Begin)
        && z.cells[n] == a.cells[n] && z.positions[n] == 0 && z.depths[n] == 0 && !z.ended[n]
}

pub proof fn begun(a:Snapshot,z:Snapshot,n:usize)
    requires wf(a),wf(z),begin_ack(a,z,n),
    ensures s::step(model(a),project(a),project(z),n,c::Rule::Begin),
{
    projection_well_formed(a);
    projection_local_edit(a,z,n);
    table_reinsert(project(a),n);
    s::total_targets_agree(project(a),n,z.control.fibers[n].committed);
    assert(tokens(n,0) =~= Seq::<nat>::empty());
}

pub open spec fn metadata_equal(a:Snapshot,z:Snapshot,n:usize) -> bool {
    a.layouts[n] == z.layouts[n] && a.codes[n] == z.codes[n] && a.initial[n] == z.initial[n]
        && a.cells[n] == z.cells[n] && a.owners[n] == z.owners[n] && a.positions[n] == z.positions[n]
        && a.depths[n] == z.depths[n] && a.ended[n] == z.ended[n]
}

pub open spec fn passive_ack(a:Snapshot,z:Snapshot,n:usize,rule:c::Rule) -> bool {
    (rule == c::Rule::Insert || rule == c::Rule::Retire || rule == c::Rule::Remove)
        && (if rule == c::Rule::Insert { n == a.allocated && z.allocated == a.allocated+1 } else { z.allocated == a.allocated })
        && c::step(a.control,z.control,n,rule)
        && forall|m:usize| c::registered(a.control,m) && c::registered(z.control,m) ==> metadata_equal(a,z,m)
}

pub proof fn passive_rule(a:Snapshot,z:Snapshot,n:usize,rule:c::Rule)
    requires wf(a),wf(z),passive_ack(a,z,n,rule),
    ensures s::step(model(a),project(a),project(z),n,rule),
{
    projection_well_formed(a);projection_well_formed(z);
    let x = project(a); let y = project(z);
    if rule == c::Rule::Insert {
        assert(row_wf(z,n));
        assert forall|i:int| 0 <= i < z.cells[n].len() implies z.cells[n][i].depth == 0 by { }
        table_domain(z.layouts[n],z.cells[n]);
        assert forall|m:usize| m != n && s::registered(x,m) implies y.tables[m] == x.tables[m]
            && y.effects[m] == x.effects[m] && y.iterators[m] == x.iterators[m] && y.accumulators[m] == x.accumulators[m] by {
            assert(c::registered(z.control,m));assert(metadata_equal(a,z,m));assert(a.control.fibers[m] == z.control.fibers[m]);
        }
    } else if rule == c::Rule::Retire {
        domain_preserved(a.control,z.control,n);
        assert(x.tables =~= y.tables) by { assert forall|m:usize| s::registered(x,m) implies x.tables[m] == y.tables[m] by { assert(metadata_equal(a,z,m)); } }
        assert(x.effects =~= y.effects);
        assert(x.iterators =~= y.iterators) by { assert forall|m:usize| s::registered(x,m) implies x.iterators[m] == y.iterators[m] by { assert(metadata_equal(a,z,m)); } }
        assert(x.accumulators =~= y.accumulators) by { assert forall|m:usize| s::registered(x,m) implies x.accumulators[m] == y.accumulators[m] by { assert(metadata_equal(a,z,m)); } }
    } else {
        assert(row_wf(a,n));
        assert forall|i:int| 0 <= i < a.cells[n].len() implies a.cells[n][i].depth == 0 by { }
        table_domain(a.layouts[n],a.cells[n]);
        assert(z.control.fibers.dom() =~= a.control.fibers.dom().remove(n)) by {
            assert forall|m:usize| z.control.fibers.dom().contains(m) == a.control.fibers.dom().remove(n).contains(m) by {
                if m != n { assert(c::registered(a.control,m) == c::registered(z.control,m)); }
            }
        }
        assert(y.tables =~= x.tables.remove(n)) by { assert forall|m:usize| s::registered(y,m) implies y.tables[m] == x.tables[m] by { assert(metadata_equal(a,z,m)); } }
        assert(y.effects =~= x.effects.remove(n));
        assert(y.iterators =~= x.iterators.remove(n)) by { assert forall|m:usize| s::registered(y,m) implies y.iterators[m] == x.iterators[m] by { assert(metadata_equal(a,z,m));assert(a.control.fibers[m] == z.control.fibers[m]); } }
        assert(y.accumulators =~= x.accumulators.remove(n)) by { assert forall|m:usize| s::registered(y,m) implies y.accumulators[m] == x.accumulators[m] by { assert(metadata_equal(a,z,m));assert(a.control.fibers[m] == z.control.fibers[m]); } }
    }
}

pub open spec fn administrative(a:Snapshot,z:Snapshot,n:usize) -> bool {
    row_frame(a,z,n) && a.control == z.control && metadata_equal(a,z,n)
}
pub open spec fn terminal_poll(a:Snapshot,z:Snapshot,n:usize) -> bool {
    row_frame(a,z,n) && a.control == z.control && c::registered(a.control,n) && a.control.fibers[n].phase == Phase::Loading
        && a.positions[n] == a.codes[n].len() && z.positions[n] == a.positions[n]
        && z.depths[n] == a.depths[n] && z.cells[n] == a.cells[n] && z.ended[n]
}

pub proof fn administrative_stutter(a:Snapshot,z:Snapshot,n:usize)
    requires wf(a),wf(z),administrative(a,z,n) || terminal_poll(a,z,n),
    ensures project(a) == project(z),
{
    let x=project(a);let y=project(z);
    assert(x.tables =~= y.tables) by { assert forall|m:usize| s::registered(x,m) implies x.tables[m] == y.tables[m] by { if m != n {assert(a.cells[m] == z.cells[m]);} } }
    assert(x.effects =~= y.effects);
    assert(x.iterators =~= y.iterators) by { assert forall|m:usize| s::registered(x,m) implies x.iterators[m] == y.iterators[m] by { if m != n {assert(a.positions[m] == z.positions[m]);} } }
    assert(x.accumulators =~= y.accumulators) by { assert forall|m:usize| s::registered(x,m) implies x.accumulators[m] == y.accumulators[m] by { if m != n {assert(a.depths[m] == z.depths[m] && a.ended[m] == z.ended[m]);} } }
}

} // verus!
