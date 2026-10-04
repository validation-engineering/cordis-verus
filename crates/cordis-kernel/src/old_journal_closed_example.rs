//! The nonempty old-journal example closes the deleted owner's actual episode.
//!
//! Source executes the old foreign inverse and then its own two-entry LIFO
//! journal. Target executes that same old foreign receipt. Both complete legal
//! lifecycle traces end with equal controls and equal observations of all tables.
#[cfg(verus_keep_ghost)]
use crate::{
    mixed_grammar as g, mixed_observational_runs as obs, old_journal_closure as closure,
    old_journal_examples as example, providing_owner_examples as base, recovery_examples as ex,
    refinement as r, semantics as s, shared_execution as sh, Phase,
};
use vstd::prelude::*;

verus! {

/// No success, final observation, or lifecycle guard is supplied by a caller.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn actual_closed_old_unload()
    ensures {
        let source=example::source();let labels=example::labels();let target=example::target();
        let foreign=g::unload(source.last(),2);let terminal=g::unload(foreign,1);let out=g::unload(target.last(),2);
        &&& g::execution(ex::library(),base::programs(),example::setup(),example::setup_labels())
        &&& example::setup().first()==g::empty::<int,bool>() && example::setup().last()==source.first()
        &&& g::step(ex::library(),base::programs(),source.last(),foreign,2,r::Rule::Unload)
        &&& g::step(ex::library(),base::programs(),foreign,terminal,1,r::Rule::Unload)
        &&& g::execution(ex::library(),base::programs(),source.push(foreign).push(terminal),labels.push((2usize,r::Rule::Unload)).push((1usize,r::Rule::Unload)))
        &&& g::step(ex::library(),base::programs(),target.last(),out,2,r::Rule::Unload)
        &&& g::execution(ex::library(),base::programs(),target.push(out),sh::labels_without(labels,1).push((2usize,r::Rule::Unload)))
        &&& g::well_formed(ex::library(),base::programs(),terminal) && g::well_formed(ex::library(),base::programs(),out)
        &&& terminal.state.control==out.state.control && obs::tables_related(ex::equality(),terminal.state,out.state)
        &&& terminal.state.tables[0usize][ex::key(0)]==10 && out.state.tables[0usize][ex::key(0)]==10
        &&& terminal.state.tables[1usize].is_empty() && out.state.tables[1usize].is_empty()
        &&& source.first().history.len()==2 && terminal.history.len()==4 && out.history.len()==2
        &&& source.last().state.accumulators[2usize]==seq![1nat] && target.last().state.accumulators[2usize]==seq![1nat]
        &&& foreign.state.tables[0usize][ex::key(0)]==15 && foreign.state.tables[1usize][ex::key(1)]==99
    },
{
    example::actual_setup();example::actual_source();example::actual_old_unload();sh::example_interface();
    reveal(example::source);
    let source=example::source();let target=example::target();let foreign=g::unload(source.last(),2);
    assert(source.last().state.control.fibers[1usize].phase==Phase::Unloading);
    closure::closed_deletion(ex::equality(),ex::library(),base::programs(),example::setup(),example::setup_labels(),source,example::labels(),foreign,1,2);
    let terminal=g::unload(foreign,1);let out=g::unload(target.last(),2);
    assert(s::registered(foreign.state,0) && foreign.state.tables[0usize].dom().contains(ex::key(0))) by {
        reveal(example::setup);reveal(base::trace);
        reveal_with_fuel(g::restore,2);
    }
    assert(crate::providing_owner_transport::controls(foreign,out,1));
    assert(s::registered(out.state,0) && out.state.tables[0usize].dom().contains(ex::key(0)));
    assert(s::registered(terminal.state,0));
    assert(terminal.state.tables[0usize].dom()==out.state.tables[0usize].dom());
    assert(ex::equality()(ex::key(0),terminal.state.tables[0usize][ex::key(0)],out.state.tables[0usize][ex::key(0)]));
}

} // verus!
