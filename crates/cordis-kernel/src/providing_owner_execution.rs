//! Constructed deletion of a providing owner with shared dependency operations.
//!
//! Private provisions are separated from every foreign declaration. Actual
//! foreign callbacks and Unloads retain their own authentic partial receipts,
//! compressed tokens and lifecycle guards. The initially inactive owner has an
//! explicitly empty table; Inactive alone is not used to infer emptiness.
#[cfg(verus_keep_ghost)]
use crate::providing_owner_transport::{advance, related};
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_lift as dep, foreign_unload as fu, mixed_grammar as g,
    mixed_observational_runs as obs, observational_grammar as og, observational_lift as ol,
    partial_independence as pi, preservation as inv, projection as p,
    providing_owner_deletion as source_proof, providing_owner_transport as target_proof,
    refinement as r, semantics as s, shared_execution as sh, shared_replay as replay,
    shared_unload_execution as history, strict_journal as sj, Phase, Port,
};
use vstd::prelude::*;

verus! {

/// Unique provided-key ownership reconstructs every table from the all-table
/// projection. No premise assumes that an omitted provision already vanished.
pub proof fn tables_from_projection<U>(eq:spec_fn(Port,U,U)->bool,a:s::State<U>,b:s::State<U>)
    requires inv::well_formed(a),inv::well_formed(b),a.control==b.control,
        pi::context_eq(eq)(p::project(a,ISet::full()),p::project(b,ISet::full())),
    ensures obs::tables_related(eq,a,b),
{
    p::unique_owner(a);p::unique_owner(b);
    assert forall|n:usize| s::registered(a,n) implies a.tables[n].dom()==b.tables[n].dom() by {
        assert(a.tables[n].dom() =~= b.tables[n].dom()) by {
            assert forall|key:Port| a.tables[n].dom().contains(key)==b.tables[n].dom().contains(key) by {
                if a.tables[n].dom().contains(key) {
                    p::lookup(a,ISet::full(),key,n);assert(p::project(b,ISet::full()).dom().contains(key));
                    let other=choose|j:usize|p::owns(b,key,j);assert(b.control.fibers[other].provisions.contains(key));assert(other==n);
                }
                if b.tables[n].dom().contains(key) {
                    p::lookup(b,ISet::full(),key,n);assert(p::project(a,ISet::full()).dom().contains(key));
                    let other=choose|j:usize|p::owns(a,key,j);assert(a.control.fibers[other].provisions.contains(key));assert(other==n);
                }
            }
        }
    }
    history::project_to_tables(eq,a,b);
}
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn landing_transport<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,owner:usize,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),source_proof::separated(source.first().state,owner),
        source_proof::fragment(programs,source,labels,source.first().history.len(),owner),g::well_formed(lib,programs,source.last()),g::well_formed(lib,programs,target),
        related(eq,source.last(),target,source.first().history.len(),owner),actor!=owner,g::step(lib,programs,source.last(),z,actor,rule),g::landing(source.last(),z,rule),
        replay::operational_mixed(programs(actor)(source.last().current[actor].unwrap())),
        pi::context_eq(eq)(sj::foreign(fu::events(fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner)),p::project(source.first().state,ISet::full())).unwrap(),p::project(target.state,ISet::full())),
    ensures {
        let out=advance(lib,programs,source.last(),z,target,actor,rule,owner);let old=g::entry(lib,programs,source.last(),actor);
        let before=fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner);let actions=before.push(fu::Action::Forward {call:fu::entry_pair(lib,programs,old,owner)});let initial=p::project(source.first().state,ISet::full());
        &&& g::step(lib,programs,target,out,actor,rule) && g::well_formed(lib,programs,out) && related(eq,z,out,source.first().history.len(),owner)
        &&& pi::context_eq(eq)(sj::foreign(fu::events(actions),initial).unwrap(),p::project(out.state,ISet::full()))
    },
{
    source_proof::fresh_historical(eq,lib,programs,source,labels,owner);
    let a=source.last();let offset=source.first().history.len();let id=a.current[actor].unwrap();let node=replay::dependent(programs(actor)(id));
    ol::frame(eq,lib,programs,a,z,actor,rule);ol::run_members(eq,lib,programs,a.state,actor,id);
    assert(programs(actor)(id)==g::Node::Dependent {node});assert(a.state.control.fibers[actor]==target.state.control.fibers[actor]);
    source_proof::next_call(eq,lib,programs,source,labels,owner,node,target.state,actor);
    target_proof::landing_from_call(eq,lib,programs,a,z,target,offset,owner,actor,rule);
    let old=g::entry(lib,programs,a,actor);let before=fu::trace_actions(lib,programs,source,labels,offset,owner);let initial=p::project(source.first().state,ISet::full());
    source_proof::actual_foreign_unload_recovery(eq,lib,programs,source,labels,owner);
    history::foreign_forward(before,fu::entry_pair(lib,programs,old,owner),initial);
}


pub proof fn append_unload_source<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,z:g::Configuration<U,I>,owner:usize,actor:usize)
    requires g::execution(lib,programs,source,labels),source_proof::fragment(programs,source,labels,source.first().history.len(),owner),actor!=owner,
        g::step(lib,programs,source.last(),z,actor,r::Rule::Unload),fu::tracked_tokens(source.last().history,source.last().state.accumulators[actor],source.first().history.len(),actor),
    ensures g::execution(lib,programs,source.push(z),labels.push((actor,r::Rule::Unload))),
        source_proof::fragment(programs,source.push(z),labels.push((actor,r::Rule::Unload)),source.first().history.len(),owner),
{
    assert forall|i:int| 0<=i<labels.push((actor,r::Rule::Unload)).len() implies g::step(lib,programs,source.push(z)[i],source.push(z)[i+1],labels.push((actor,r::Rule::Unload))[i].0,labels.push((actor,r::Rule::Unload))[i].1) by {
        if i<labels.len() {assert(source.push(z)[i]==source[i]);assert(source.push(z)[i+1]==source[i+1]);} else {assert(i==labels.len());}
    }
    assert forall|i:int| 0<=i<labels.push((actor,r::Rule::Unload)).len() && g::landing(source.push(z)[i],source.push(z)[i+1],labels.push((actor,r::Rule::Unload))[i].1)
        implies {
            let actor=labels.push((actor,r::Rule::Unload))[i].0;let node=programs(actor)(source.push(z)[i].current[actor].unwrap());
            source_proof::table_node(node) && (actor!=owner ==> replay::operational_mixed(node))
        } by {
        assert(i<labels.len());assert(source.push(z)[i]==source[i]);assert(source.push(z)[i+1]==source[i+1]);
    }
    assert forall|i:int| #![trigger labels.push((actor,r::Rule::Unload))[i]] 0<=i<labels.push((actor,r::Rule::Unload)).len() implies {
        let label=labels.push((actor,r::Rule::Unload))[i];
        &&& label.1!=r::Rule::Insert && label.1!=r::Rule::Remove
        &&& (label.1==r::Rule::Unload ==> label.0!=owner && fu::tracked_tokens(source.push(z)[i].history,source.push(z)[i].state.accumulators[label.0],source.first().history.len(),label.0))
    } by {if i<labels.len() {assert(source.push(z)[i]==source[i]);} else {assert(i==labels.len());}}
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn unload_transport<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,owner:usize,actor:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),source_proof::separated(source.first().state,owner),
        source_proof::fragment(programs,source,labels,source.first().history.len(),owner),g::well_formed(lib,programs,source.last()),g::well_formed(lib,programs,target),
        related(eq,source.last(),target,source.first().history.len(),owner),actor!=owner,g::step(lib,programs,source.last(),z,actor,r::Rule::Unload),
        fu::tracked_tokens(source.last().history,source.last().state.accumulators[actor],source.first().history.len(),actor),
        pi::context_eq(eq)(sj::foreign(fu::events(fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner)),p::project(source.first().state,ISet::full())).unwrap(),p::project(target.state,ISet::full())),
    ensures {
        let out=g::unload(target,actor);let actions=fu::trace_actions(lib,programs,source.push(z),labels.push((actor,r::Rule::Unload)),source.first().history.len(),owner);let initial=p::project(source.first().state,ISet::full());
        &&& g::step(lib,programs,target,out,actor,r::Rule::Unload) && g::well_formed(lib,programs,out) && related(eq,z,out,source.first().history.len(),owner)
        &&& pi::context_eq(eq)(sj::foreign(fu::events(actions),initial).unwrap(),p::project(out.state,ISet::full()))
    },
{
    source_proof::fresh_historical(eq,lib,programs,source,labels,owner);
    let a=source.last();let offset=source.first().history.len();let tokens=a.state.accumulators[actor];let initial=p::project(source.first().state,ISet::full());
    let prefix=fu::trace_actions(lib,programs,source,labels,offset,owner);let reference=sj::foreign(fu::events(prefix),initial).unwrap();
    append_unload_source(lib,programs,source,labels,z,owner,actor);
    source_proof::actual_source(eq,lib,programs,source,labels,owner);source_proof::fresh_historical(eq,lib,programs,source,labels,owner);
    source_proof::actual_foreign_unload_recovery(eq,lib,programs,source,labels,owner);
    source_proof::actual_foreign_unload_recovery(eq,lib,programs,source.push(z),labels.push((actor,r::Rule::Unload)),owner);
    let actions=fu::trace_actions(lib,programs,source.push(z),labels.push((actor,r::Rule::Unload)),offset,owner);
    assert(source.push(z).drop_last() =~= source);assert(labels.push((actor,r::Rule::Unload)).drop_last() =~= labels);
    assert(actions==prefix+fu::inverse_actions(tokens,offset));
    history::foreign_inverse_word(lib,programs,a.history,tokens,offset,owner,actor,prefix,initial);
    assert forall|i:int| 0<=i<tokens.len() implies history::simple(#[trigger] a.history[tokens[i] as int].landed.receipt) by {
        let token=tokens[i];assert(offset<=token<a.history.len());
        assert(source_proof::historical(lib,programs,a.history[token as int],owner,source.first().state.control.fibers[owner].provisions));
        assert(g::owner(a.history[token as int].landed.receipt)==actor);
    }
    target_proof::restore_transport(eq,a.history,target.history,tokens,offset,owner,actor,a.state,target.state,reference);
    target_proof::restore_domains(a.history,tokens,offset,a.state,actor);
    assert(target.state.accumulators[actor]==history::rename(a.history,offset,owner,tokens));
    target_proof::no_users(a,target,owner,actor);let out=g::unload(target,actor);assert(g::step(lib,programs,target,out,actor,r::Rule::Unload));
    ol::configuration_preservation(eq,lib,programs,target,out,actor,r::Rule::Unload);ol::frame(eq,lib,programs,a,z,actor,r::Rule::Unload);ol::frame(eq,lib,programs,target,out,actor,r::Rule::Unload);
    assert forall|n:usize| s::registered(z.state,n) && n!=owner implies {
        &&& z.state.tables[n].dom()==out.state.tables[n].dom()
        &&& (n!=owner ==> z.state.control.fibers[n]==out.state.control.fibers[n] && z.current[n]==out.current[n])
    } by {assert(s::registered(a.state,n));assert(s::registered(target.state,n));}
    assert forall|n:usize| s::registered(z.state,n) && n!=owner implies out.state.accumulators[n]==history::rename(z.history,offset,owner,z.state.accumulators[n]) by {
        assert(s::registered(a.state,n));if n==actor {history::rename_laws(a.history,offset,owner,Seq::empty(),0);}
    }
    let restored=g::restore(target.history,target.state.accumulators[actor],target.state,actor).unwrap();p::unique_owner(restored);
    p::lifecycle_edit(restored,actor,Phase::Inactive,ISet::empty(),None,Seq::empty(),ISet::full());
}

#[verifier::opaque]
pub open spec fn delete<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)->Seq<g::Configuration<U,I>>
    decreases labels.len(),
{
    if labels.len()==0 {seq![source.first()]} else {
        let before=delete(lib,programs,source.drop_last(),labels.drop_last(),owner);let label=labels.last();
        if sh::keep(label.0,label.1,owner) {before.push(advance(lib,programs,source[source.len()-2],source.last(),before.last(),label.0,label.1,owner))}
        else {before}
    }
}

/// Every kept transition is a real target lifecycle transition, including
/// target Unload with compressed tokens and its own actual returned inverses.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn delete_execution<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),source_proof::separated(source.first().state,owner),
        source_proof::fragment(programs,source,labels,source.first().history.len(),owner),s::registered(source.first().state,owner),
        source.first().state.tables[owner].is_empty(),source.first().state.control.fibers[owner].phase==Phase::Inactive,
    ensures {
        let target=delete(lib,programs,source,labels,owner);let kept=sh::labels_without(labels,owner);let actions=fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner);let initial=p::project(source.first().state,ISet::full());
        &&& g::execution(lib,programs,target,kept) && target.first()==source.first()
        &&& related(eq,source.last(),target.last(),source.first().history.len(),owner) && g::well_formed(lib,programs,source.last())
        &&& forall|i:int| 0<=i<target.len() ==> g::well_formed(lib,programs,target[i])
        &&& sj::foreign(fu::events(actions),initial).is_some()
        &&& pi::context_eq(eq)(sj::foreign(fu::events(actions),initial).unwrap(),p::project(target.last().state,ISet::full()))
    },
    decreases labels.len(),
{
    reveal(delete);reveal(sh::labels_without);
    let target=delete(lib,programs,source,labels,owner);let kept=sh::labels_without(labels,owner);let offset=source.first().history.len();
    let actions=fu::trace_actions(lib,programs,source,labels,offset,owner);let initial=p::project(source.first().state,ISet::full());
    source_proof::actual_foreign_unload_recovery(eq,lib,programs,source,labels,owner);
    if labels.len()==0 {
        assert(source.len()==1);assert(source.first()==source.last());target_proof::initial_related(lib,programs,source.first(),owner,eq);
        replay::context_equivalence(eq,lib);assert(pi::context_eq(eq)(initial,initial));
    } else {
        let states=source.drop_last();let previous=labels.drop_last();let label=labels.last();let a=states.last();let z=source.last();let actor=label.0;let rule=label.1;
        assert(g::execution(lib,programs,states,previous));assert(source_proof::fragment(programs,states,previous,offset,owner));
        delete_execution(eq,lib,programs,states,previous,owner);
        source_proof::fresh_historical(eq,lib,programs,states,previous,owner);
        let before=delete(lib,programs,states,previous,owner);let earlier=sh::labels_without(previous,owner);let input=before.last();
        let prefix=fu::trace_actions(lib,programs,states,previous,offset,owner);let out=advance(lib,programs,a,z,input,actor,rule,owner);
        ol::frame(eq,lib,programs,a,z,actor,rule);ol::configuration_preservation(eq,lib,programs,a,z,actor,rule);
        if g::landing(a,z,rule) {
            let entry=g::entry(lib,programs,a,actor);let call=fu::entry_pair(lib,programs,entry,owner);
            assert(actions =~= prefix.push(fu::Action::Forward {call}));assert(actions.drop_last() =~= prefix);assert(fu::events(actions).drop_last() =~= fu::events(prefix));
            if actor==owner {target_proof::own_landing(eq,lib,programs,a,z,input,offset,owner,rule);assert(call.own);}
            else {landing_transport(eq,lib,programs,states,previous,z,input,owner,actor,rule);}
        } else if rule==r::Rule::Unload {
            assert(actor!=owner);assert(states.push(z) =~= source);assert(previous.push((actor,r::Rule::Unload)) =~= labels);
            unload_transport(eq,lib,programs,states,previous,z,input,owner,actor);
        } else {
            target_proof::control_transport(eq,lib,programs,a,z,input,offset,owner,actor,rule);
            assert(actions =~= prefix.push(fu::Action::Identity));assert(actions.drop_last() =~= prefix);assert(fu::events(actions).drop_last() =~= fu::events(prefix));
        }
        if sh::keep(actor,rule,owner) {
            assert(target==before.push(out));assert(kept==earlier.push(label));
            assert forall|i:int| 0<=i<target.len() implies g::well_formed(lib,programs,target[i]) by {
                if i<before.len() {assert(target[i]==before[i]);} else {assert(i==before.len());}
            }
            assert(g::execution(lib,programs,target,kept)) by {
                assert forall|i:int| 0<=i<kept.len() implies g::step(lib,programs,target[i],target[i+1],kept[i].0,kept[i].1) by {
                    if i<earlier.len() {assert(target[i]==before[i]);assert(target[i+1]==before[i+1]);}
                    else {assert(i==earlier.len());assert(target[i]==before.last());}
                }
            }
        }
    }
}
pub open spec fn prefix_valid<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize,i:int)->bool {
    let states=source.take(i+1);let steps=labels.take(i);let target=delete(lib,programs,states,steps,owner);
    g::execution(lib,programs,target,sh::labels_without(steps,owner)) && target.first()==source.first() && related(eq,source[i],target.last(),source.first().history.len(),owner)
}
pub proof fn every_prefix<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),source_proof::separated(source.first().state,owner),
        source_proof::fragment(programs,source,labels,source.first().history.len(),owner),s::registered(source.first().state,owner),source.first().state.tables[owner].is_empty(),source.first().state.control.fibers[owner].phase==Phase::Inactive,
    ensures forall|i:int| 0<=i<source.len() ==> #[trigger] prefix_valid(eq,lib,programs,source,labels,owner,i),
{
    assert forall|i:int| 0<=i<source.len() implies #[trigger] prefix_valid(eq,lib,programs,source,labels,owner,i) by {
        let states=source.take(i+1);let steps=labels.take(i);
        assert(g::execution(lib,programs,states,steps));assert(source_proof::fragment(programs,states,steps,source.first().history.len(),owner));
        assert(states.first()==source.first());assert(states.last()==source[i]);delete_execution(eq,lib,programs,states,steps,owner);
    }
}

/// The closed episode is removed from an actual lifecycle execution. Every
/// provider table has the same final observation, while source and target
/// keep authentic, differently indexed histories and returned inverse maps.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn terminal_deletion<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),source_proof::separated(source.first().state,owner),
        source_proof::fragment(programs,source,labels,source.first().history.len(),owner),s::registered(source.first().state,owner),source.first().state.tables[owner].is_empty(),source.first().state.control.fibers[owner].phase==Phase::Inactive,
        source.last().state.control.fibers[owner].phase==Phase::Unloading,
    ensures {
        let last=source.last();let terminal=g::unload(last,owner);let target=delete(lib,programs,source,labels,owner);
        &&& g::step(lib,programs,last,terminal,owner,r::Rule::Unload) && g::well_formed(lib,programs,terminal)
        &&& g::execution(lib,programs,source.push(terminal),labels.push((owner,r::Rule::Unload)))
        &&& g::execution(lib,programs,target,sh::labels_without(labels.push((owner,r::Rule::Unload)),owner)) && target.first()==source.first()
        &&& obs::tables_related(eq,terminal.state,target.last().state)
        &&& forall|i:int| 0<=i<target.len() ==> g::well_formed(lib,programs,target[i])
    },
{
    delete_execution(eq,lib,programs,source,labels,owner);source_proof::terminal_with_foreign_unloads(eq,lib,programs,source,labels,owner);
    source_proof::actual_journal(eq,lib,programs,source,labels,owner);source_proof::actual_foreign_unload_recovery(eq,lib,programs,source,labels,owner);
    let last=source.last();let terminal=g::unload(last,owner);let target=delete(lib,programs,source,labels,owner);let out=target.last();
    source_proof::restore_definedness(last.history,last.state.accumulators[owner],last.state,owner);replay::context_equivalence(eq,lib);
    assert(target_proof::controls(last,out,owner));
    assert forall|n:usize| terminal.state.control.fibers.dom().contains(n) implies #[trigger] terminal.state.control.fibers[n]==out.state.control.fibers[n] by {
        assert(s::registered(last.state,n));
        if n==owner {assert(r::interface_same(last.state.control.fibers[n],out.state.control.fibers[n]));assert(terminal.state.control.fibers[n].committed =~= out.state.control.fibers[n].committed);}
        else {assert(last.state.control.fibers[n]==out.state.control.fibers[n]);}
    }
    assert(terminal.state.control.fibers.dom() =~= last.state.control.fibers.dom());assert(terminal.state.control.fibers.dom()==out.state.control.fibers.dom());
    assert(terminal.state.control.fibers =~= out.state.control.fibers);assert(terminal.state.control==out.state.control);
    let actions=fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner);let initial=p::project(source.first().state,ISet::full());
    assert(pi::context_eq(eq)(p::project(terminal.state,ISet::full()),sj::foreign(fu::events(actions),initial).unwrap()));
    assert(pi::context_eq(eq)(p::project(terminal.state,ISet::full()),p::project(out.state,ISet::full())));
    tables_from_projection(eq,terminal.state,out.state);
    reveal(sh::labels_without);assert(labels.push((owner,r::Rule::Unload)).drop_last() =~= labels);
    assert(g::execution(lib,programs,source.push(terminal),labels.push((owner,r::Rule::Unload)))) by {
        assert forall|i:int| 0<=i<labels.push((owner,r::Rule::Unload)).len() implies g::step(lib,programs,source.push(terminal)[i],source.push(terminal)[i+1],labels.push((owner,r::Rule::Unload))[i].0,labels.push((owner,r::Rule::Unload))[i].1) by {
            if i<labels.len() {assert(source.push(terminal)[i+1]==source[i+1]);} else {assert(i==labels.len());}
        }
    }
}


} // verus!
