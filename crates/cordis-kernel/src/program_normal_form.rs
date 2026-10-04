//! Schedule independence for successful executions of the concrete private-cell
//! language. Orchestration inputs are extracted from actual acknowledgements;
//! the terminal service values and inverse journals are derived from code.
#[cfg(verus_keep_ghost)]
use crate::{
    global, program, program_refinement as p, program_trace as t, refinement as c, semantics as s,
    Phase,
};
use crate::{program::Instruction, resources::Cell, Port};
use vstd::prelude::*;

verus! {
pub struct Input {
    pub parent:Option<usize>,
    pub dependencies:ISet<Port>,
    pub provisions:ISet<Port>,
    pub retired:bool,
    pub code:Seq<Instruction>,
    pub layout:Seq<Port>,
    pub initial:Seq<Cell>,
    pub owner:u64,
}

pub open spec fn input(x:p::Snapshot,n:usize) -> Input {
    Input {parent:x.control.fibers[n].parent,dependencies:x.control.fibers[n].dependencies,
        provisions:x.control.fibers[n].provisions,retired:x.control.fibers[n].retired,
        code:x.codes[n],layout:x.layouts[n],initial:x.initial[n],owner:x.owners[n]}
}
pub open spec fn inputs(x:p::Snapshot) -> IMap<usize,Input> {
    IMap::new(|n:usize| c::registered(x.control,n),|n:usize| input(x,n))
}
pub proof fn input_lookup(x:p::Snapshot,n:usize)
    requires c::registered(x.control,n),
    ensures inputs(x).dom().contains(n), inputs(x)[n] == input(x,n),
{ }

pub open spec fn retire(x:Input) -> Input {
    Input {parent:x.parent,dependencies:x.dependencies,provisions:x.provisions,retired:true,
        code:x.code,layout:x.layout,initial:x.initial,owner:x.owner}
}

/// Only Insert has a payload. Lifecycle scheduling never enters this log.
pub enum InputEvent { Insert(usize,Input), Retire(usize), Remove(usize) }
pub open spec fn input_event(z:p::Snapshot,e:t::Event) -> Option<InputEvent> {
    match e {
        t::Event::Insert(n) => Some(InputEvent::Insert(n,input(z,n))),
        t::Event::Retire(n) => Some(InputEvent::Retire(n)),
        t::Event::Remove(n) => Some(InputEvent::Remove(n)),
        _ => None,
    }
}
pub open spec fn apply(x:IMap<usize,Input>,e:InputEvent) -> IMap<usize,Input> {
    match e {
        InputEvent::Insert(n,row) => x.insert(n,row),
        InputEvent::Retire(n) => x.insert(n,retire(x[n])),
        InputEvent::Remove(n) => x.remove(n),
    }
}
pub open spec fn fold(x:IMap<usize,Input>,events:Seq<InputEvent>) -> IMap<usize,Input>
    decreases events.len(),
{
    if events.len() == 0 {x} else {apply(fold(x,events.drop_last()),events.last())}
}
pub open spec fn orchestration(states:Seq<p::Snapshot>,events:Seq<t::Event>) -> Seq<InputEvent>
    recommends states.len() == events.len()+1,
    decreases events.len(),
{
    if events.len() == 0 {Seq::empty()} else {
        let prefix=orchestration(states.drop_last(),events.drop_last());
        match input_event(states.last(),events.last()) {Some(e) => prefix.push(e),None => prefix}
    }
}

pub proof fn acknowledgement_inputs(a:p::Snapshot,z:p::Snapshot,e:t::Event)
    requires p::wf(a),p::wf(z),t::ack(a,z,e),
    ensures inputs(z) == match input_event(z,e) {Some(ie) => apply(inputs(a),ie),None => inputs(a)},
{
    t::acknowledgement_frame(a,z,e);
    if let t::Event::Land(n,program::LandOutcome::Diverted) = e {
        let middle=choose|middle:p::Snapshot| p::wf(middle)
            && (p::landed(a,middle,n) || p::terminal_poll(a,middle,n)) && p::depart_ack(middle,z,n);
        assert(global::same_input(a.control,z.control));
    }
    let expected=match input_event(z,e) {Some(ie) => apply(inputs(a),ie),None => inputs(a)};
    assert(inputs(z) =~= expected) by {
        assert forall|n:usize| inputs(z).dom().contains(n) == expected.dom().contains(n) by { }
        assert forall|n:usize| inputs(z).dom().contains(n) implies inputs(z)[n] == expected[n] by {
            if n != t::actor(e) { assert(a.control.fibers[n] == z.control.fibers[n]); }
            if c::registered(a.control,n) { assert(t::configuration_equal(a,z,n)); }
        }
    }
}

pub proof fn trace_inputs(states:Seq<p::Snapshot>,events:Seq<t::Event>)
    requires t::raw_execution(states,events),
    ensures inputs(states.last()) == fold(inputs(states.first()),orchestration(states,events)),
    decreases events.len(),
{
    if events.len() > 0 {
        let xs=states.drop_last();let es=events.drop_last();
        assert(t::raw_execution(xs,es));trace_inputs(xs,es);
        acknowledgement_inputs(xs.last(),states.last(),events.last());
        if input_event(states.last(),events.last()).is_some() {
            let prefix=orchestration(xs,es);
            assert(orchestration(states,events).drop_last() =~= prefix);
        }
    }
}

/// Once the actual instruction pointer reaches the end, prefix evaluation is
/// stationary. The depth invariant records that no dummy stages were counted.
pub proof fn terminal_stable(code:Seq<Instruction>,owner:u64,initial:Seq<Cell>,at:nat,more:nat)
    requires program::prefix(code,owner,initial,at).next >= code.len(),
    ensures program::prefix(code,owner,initial,at+more) == program::prefix(code,owner,initial,at),
    decreases more,
{
    if more > 0 { terminal_stable(code,owner,initial,at,(more-1) as nat); }
}

pub proof fn terminal_depth_unique(code:Seq<Instruction>,owner:u64,initial:Seq<Cell>,a:nat,b:nat)
    requires program::prefix(code,owner,initial,a).next == code.len(),
        program::prefix(code,owner,initial,b).next == code.len(),
        a > 0 ==> program::prefix(code,owner,initial,(a-1) as nat).next < code.len(),
        b > 0 ==> program::prefix(code,owner,initial,(b-1) as nat).next < code.len(),
    ensures a == b,
{
    if a < b { terminal_stable(code,owner,initial,a,(b-1-a) as nat); }
    if b < a { terminal_stable(code,owner,initial,b,(a-1-b) as nat); }
}

pub proof fn table_lookup(x:p::Snapshot,n:usize)
    requires c::registered(x.control,n),
    ensures p::project(x).tables.dom().contains(n),
        p::project(x).tables[n] == p::table(x.layouts[n],x.cells[n]),
{ }

pub proof fn quiet_row_equal(a:p::Snapshot,b:p::Snapshot,n:usize)
    requires p::wf(a),p::wf(b),a.control == b.control,c::quiet(a.control),
        c::registered(a.control,n),input(a,n) == input(b,n),
    ensures a.cells[n] == b.cells[n],a.depths[n] == b.depths[n],
        p::extra_terminal(a,n) == p::extra_terminal(b,n),
{
    assert(p::row_wf(a,n));assert(p::row_wf(b,n));
    if a.control.fibers[n].phase == Phase::Active {
        terminal_depth_unique(a.codes[n],a.owners[n],a.initial[n],a.depths[n],b.depths[n]);
    } else {assert(a.control.fibers[n].phase == Phase::Inactive);}
}

#[verifier::rlimit(20)]
pub proof fn quiet_projection_unique(a:p::Snapshot,b:p::Snapshot,ranks:Seq<nat>)
    requires p::wf(a),p::wf(b),c::quiet(a.control),c::quiet(b.control),
        inputs(a) == inputs(b),global::precedence_ranking(a.control,ranks),
    ensures p::project(a) == p::project(b),
{
    assert forall|n:usize| c::registered(a.control,n) implies input(a,n) == input(b,n) by {
        assert(inputs(a).dom().contains(n));assert(inputs(b).dom().contains(n));
        assert(c::registered(b.control,n));
        input_lookup(a,n);input_lookup(b,n);
    }
    assert(inputs(a).dom() =~= a.control.fibers.dom());
    assert(inputs(b).dom() =~= b.control.fibers.dom());
    assert(global::same_input(a.control,b.control)) by {
        assert forall|n:usize| c::registered(a.control,n) implies
            c::interface_same(a.control.fibers[n],b.control.fibers[n])
                && a.control.fibers[n].retired == b.control.fibers[n].retired by {
            assert(c::registered(b.control,n));
            assert(inputs(a)[n] == inputs(b)[n]);
            assert(input(a,n) == input(b,n));
        }
    }
    global::quiet_control_unique(a.control,b.control,ranks);
    assert forall|n:usize| c::registered(a.control,n) implies
        a.cells[n] == b.cells[n] && a.depths[n] == b.depths[n]
            && p::extra_terminal(a,n) == p::extra_terminal(b,n) by {
        quiet_row_equal(a,b,n);
    }
    assert(p::project(a).tables =~= p::project(b).tables) by {
        assert forall|n:usize| c::registered(a.control,n) implies p::project(a).tables[n] == p::project(b).tables[n] by {
            assert(c::registered(b.control,n));
            table_lookup(a,n);table_lookup(b,n);
            assert(inputs(a)[n] == inputs(b)[n]);
            assert(input(a,n) == input(b,n));
            assert(a.layouts[n] == b.layouts[n]);
            quiet_row_equal(a,b,n);
        }
    }
    assert(p::project(a).effects =~= p::project(b).effects);
    assert(p::project(a).iterators =~= p::project(b).iterators);
    assert(p::project(a).accumulators =~= p::project(b).accumulators);
}

/// Two actual API histories with identical extracted orchestration and initial
/// input have the same quiet full state. No equality of endpoint values,
/// active sets, iterator histories or inverse journals is assumed.
pub proof fn driver_quiet_confluence(a:Seq<p::Snapshot>,ea:Seq<t::Event>,b:Seq<p::Snapshot>,eb:Seq<t::Event>,ranks:Seq<nat>)
    requires t::raw_execution(a,ea),t::raw_execution(b,eb),
        inputs(a.first()) == inputs(b.first()),orchestration(a,ea) == orchestration(b,eb),
        c::quiet(a.last().control),c::quiet(b.last().control),global::precedence_ranking(a.last().control,ranks),
    ensures p::project(a.last()) == p::project(b.last()),
        s::reaches(p::model(t::history_catalog(a)),p::project(a.first()),p::project(a.last()),t::paper_labels(a,ea).len()),
        s::reaches(p::model(t::history_catalog(b)),p::project(b.first()),p::project(b.last()),t::paper_labels(b,eb).len()),
{
    trace_inputs(a,ea);trace_inputs(b,eb);
    quiet_projection_unique(a.last(),b.last(),ranks);
    t::driver_trace_refinement(a,ea);t::driver_trace_refinement(b,eb);
}
} // verus!
