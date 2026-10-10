//! Retained foreign child creation and retirement across a deleted table owner.
//!
//! Fresh identities, Insert guards, actual roots and actual Child receipts are
//! transported through the common registry. Identity all-table projection only
//! supplies the value-batch part: lifecycle guards and journal retention are
//! separately proved. This is the strict guarded mixed grammar, not a claim
//! that Child has the original paper's unrestricted component-domain witness.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, dependent_lift as dep, foreign_unload as fu,
    internal_old_unload as batch_state, mixed_grammar as g, mixed_observational_runs as obs,
    observational_grammar as og, observational_lift as ol, projection as p,
    providing_owner_deletion as own, providing_owner_transport as transport, refinement as r,
    semantics as s, shared_execution as sh, shared_unload_execution as history, Phase, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn child_node<A,X,U,B,I>(node:g::Node<A,X,U,B,I>)->bool {match node {g::Node::Child {..}=>true,_=>false}}
pub open spec fn guard<A,X,U,B,I>(programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,actor:usize,owner:usize)->bool {
    actor!=owner && match programs(actor)(a.current[actor].unwrap()) {
        g::Node::Child {dependencies,..}=>dependencies.disjoint(a.state.control.fibers[owner].provisions),_=>false,
    }
}
pub open spec fn with_state<U,I>(a:g::Configuration<U,I>,state:s::State<U>)->g::Configuration<U,I> {
    g::Configuration {state,roots:a.roots,current:a.current,history:a.history}
}

/// The target creation is derived from the source's real successful call.
pub proof fn actual_call<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,target:g::Configuration<U,I>,actor:usize,owner:usize)
    requires transport::controls(a,target,owner),actor!=owner,s::registered(a.state,actor),
        child_node(programs(actor)(a.current[actor].unwrap())),g::run(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor).is_some(),
    ensures {
        let left=g::entry(lib,programs,a,actor);let right=g::entry(lib,programs,target,actor);
        &&& g::run(lib,programs(actor)(target.current[actor].unwrap()),target.state,actor).is_some()
        &&& left.iterator==right.iterator && left.landed.receipt==right.landed.receipt
        &&& left.landed.next==right.landed.next && left.landed.spawn==right.landed.spawn
    },
{
    assert(a.current[actor]==target.current[actor]);
    if let g::Node::Child {child,dependencies,provisions,root,next}=programs(actor)(a.current[actor].unwrap()) {
        let out=g::create(target.state,actor,child,dependencies,provisions);
        assert forall|n:usize,key:Port|r::registered(target.state.control,n) && target.state.control.fibers[n].provisions.contains(key)
            implies !out.control.fibers[child].provisions.contains(key) by {
            assert(s::registered(a.state,n));if n==owner {assert(a.state.control.fibers[n].provisions==target.state.control.fibers[n].provisions);}
        }
        assert(r::frame(target.state.control,out.control,child));
        assert(r::step(target.state.control,out.control,child,r::Rule::Insert));
    }
}

/// Owner journal pinning uses its unchanged interface and committed view.
/// The history may append an authentic foreign entry; old token inputs stay put.
pub proof fn owner_pins<U,I>(a:g::Configuration<U,I>,z:g::Configuration<U,I>,owner:usize)
    requires s::registered(a.state,owner),s::registered(z.state,owner),
        r::interface_same(a.state.control.fibers[owner],z.state.control.fibers[owner]),a.state.control.fibers[owner].committed==z.state.control.fibers[owner].committed,
        a.state.accumulators[owner]==z.state.accumulators[owner],own::pinned_tokens(a.history,a.state.accumulators[owner],a.state,owner),
        a.history.len()<=z.history.len(),forall|i:int|0<=i<a.history.len() ==> z.history[i]==a.history[i],
    ensures own::pinned_tokens(z.history,z.state.accumulators[owner],z.state,owner),
        sh::receipt_word(z.history,z.state.accumulators[owner])==sh::receipt_word(a.history,a.state.accumulators[owner]),
{
    sh::resolution_frame(a.state,z.state,owner);
    assert forall|i:int|0<=i<a.state.accumulators[owner].len() implies a.history[a.state.accumulators[owner][i] as int].landed.receipt==z.history[a.state.accumulators[owner][i] as int].landed.receipt by {
        assert(a.state.accumulators[owner][i]<a.history.len());
    }
    sh::receipt_word_extensional(a.history,z.history,a.state.accumulators[owner]);
    assert forall|i:int|0<=i<z.state.accumulators[owner].len() implies z.state.accumulators[owner][i]<z.history.len()
        && own::pinned(#[trigger] z.history[z.state.accumulators[owner][i] as int].landed.receipt,z.state,owner) by {
        let token=z.state.accumulators[owner][i];assert(own::pinned(a.history[token as int].landed.receipt,a.state,owner));
        match a.history[token as int].landed.receipt {g::Receipt::Table {receipt}=>{match receipt.inverse {crate::grammar_lift::Inverse::Operation {key,..}=>{assert(crate::grammar_lift::resolve(a.state,owner,key)==crate::grammar_lift::resolve(z.state,owner,key));},_=>{}}},_=>{},}
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(35)]
pub proof fn source_landing<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,owner:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,z,actor,rule),g::landing(a,z,rule),
        own::separated(a.state,owner),guard(programs,a,actor,owner),
    ensures g::well_formed(lib,programs,z),own::separated(z.state,owner),
        z.state.control.fibers[owner]==a.state.control.fibers[owner],z.state.tables[owner]==a.state.tables[owner],z.state.accumulators[owner]==a.state.accumulators[owner],
        z.current[owner]==a.current[owner],z.roots[owner]==a.roots[owner],
        p::project(z.state,ISet::full())==p::project(a.state,ISet::full()),
        forall|n:usize|s::registered(a.state,n) ==> s::registered(z.state,n) && r::interface_same(a.state.control.fibers[n],z.state.control.fibers[n]),
{
    ol::frame(eq,lib,programs,a,z,actor,rule);ol::configuration_preservation(eq,lib,programs,a,z,actor,rule);
    if let g::Node::Child {child,dependencies,provisions,..}=programs(actor)(a.current[actor].unwrap()) {
        let landed=g::entry(lib,programs,a,actor).landed.state;assert(!s::registered(a.state,child));assert(child!=owner);assert(child!=actor);
        ol::run_admissible(eq,lib,programs(actor)(a.current[actor].unwrap()),a.state,actor);
        p::empty_insertion(a.state,landed,child,ISet::full());p::unique_owner(landed);
        p::lifecycle_edit(landed,actor,z.state.control.fibers[actor].phase,a.state.control.fibers[actor].committed,z.state.iterators[actor],z.state.accumulators[actor],ISet::full());
        assert forall|n:usize|s::registered(z.state,n) && n!=owner implies dep::declarations(z.state,n).disjoint(z.state.control.fibers[owner].provisions) by {
            if n==child {
                assert(provisions.disjoint(a.state.control.fibers[owner].provisions)) by {
                    assert forall|key:Port|provisions.contains(key) implies !a.state.control.fibers[owner].provisions.contains(key) by {assert(s::registered(a.state,owner));}
                }
            } else {assert(s::registered(a.state,n));assert(dep::declarations(a.state,n)==dep::declarations(z.state,n));}
        }
    }
}

/// Both configurations append their own actual child Entry, not a copied input.
#[verifier::spinoff_prover]
#[verifier::rlimit(45)]
pub proof fn landing_transport<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,offset:nat,owner:usize,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::well_formed(lib,programs,target),transport::related(eq,a,target,offset,owner),
        own::separated(a.state,owner),g::step(lib,programs,a,z,actor,rule),g::landing(a,z,rule),guard(programs,a,actor,owner),
    ensures {
        let out=transport::advance(lib,programs,a,z,target,actor,rule,owner);
        &&& g::step(lib,programs,target,out,actor,rule) && g::well_formed(lib,programs,out) && transport::related(eq,z,out,offset,owner)
        &&& own::separated(z.state,owner) && g::well_formed(lib,programs,z)
        &&& p::project(z.state,ISet::full())==p::project(a.state,ISet::full()) && p::project(out.state,ISet::full())==p::project(target.state,ISet::full())
        &&& g::entry(lib,programs,a,actor).landed.receipt==g::entry(lib,programs,target,actor).landed.receipt
        &&& g::entry(lib,programs,a,actor).landed.spawn==g::entry(lib,programs,target,actor).landed.spawn
    },
{
    source_landing(eq,lib,programs,a,z,actor,rule,owner);ol::frame(eq,lib,programs,a,z,actor,rule);
    actual_call(lib,programs,a,target,actor,owner);transport::publication(a,target,owner,actor,a.state.control.fibers[actor].committed);
    let out=transport::advance(lib,programs,a,z,target,actor,rule,owner);
    assert(g::step(lib,programs,target,out,actor,rule));ol::configuration_preservation(eq,lib,programs,target,out,actor,rule);ol::frame(eq,lib,programs,target,out,actor,rule);
    transport::separated_target(a,target,owner);source_landing(eq,lib,programs,target,out,actor,rule,owner);
    let old=g::entry(lib,programs,a,actor);let new=g::entry(lib,programs,target,actor);
    assert(obs::receipt_related(eq,old.landed.receipt,new.landed.receipt));history::histories_push(eq,a.history,target.history,old,new,offset,owner);
    if let g::Node::Child {child,..}=programs(actor)(a.current[actor].unwrap()) {
        assert(child!=owner);assert(child!=actor);assert(!s::registered(a.state,child));
        assert(z.state.control.fibers.dom() =~= out.state.control.fibers.dom());
        assert forall|n:usize|s::registered(z.state,n) && n!=owner implies {
            &&& z.state.tables[n].dom()==out.state.tables[n].dom()
            &&& z.state.control.fibers[n]==out.state.control.fibers[n] && z.current[n]==out.current[n]
        } by {if n!=child {assert(s::registered(a.state,n));}}
        assert forall|n:usize|s::registered(z.state,n) && n!=owner implies out.state.accumulators[n]==history::rename(z.history,offset,owner,z.state.accumulators[n]) by {
            if n==child {history::rename_laws(z.history,offset,owner,Seq::empty(),0);}
            else {
                assert(s::registered(a.state,n));assert forall|i:int|0<=i<a.state.accumulators[n].len() implies a.state.accumulators[n][i]<=a.history.len() by {assert(a.state.accumulators[n][i]<a.history.len());}
                if n==actor {history::rename_laws(a.history,offset,owner,a.state.accumulators[n],a.history.len());history::rename_append(a.history,old,offset,owner,a.state.accumulators[n].push(a.history.len()));}
                else {history::rename_append(a.history,old,offset,owner,a.state.accumulators[n]);}
            }
        }
    }
}

/// This is a value erasure of the genuine successful creation. The flat
/// identity does not assert that the state-level Child inverse is total.
pub proof fn call_projects<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,actor:usize,owner:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),child_node(programs(actor)(a.current[actor].unwrap())),
        g::run(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor).is_some(),
    ensures {
        let entry=g::entry(lib,programs,a,actor);let call=fu::entry_pair(lib,programs,entry,owner);
        &&& call.forward==fu::identity() && call.inverse==fu::identity() && call.own==(actor==owner)
        &&& (call.forward)(p::project(a.state,ISet::full()))==Some(p::project(entry.landed.state,ISet::full()))
        &&& g::undo(entry.landed.receipt,entry.landed.state).is_some()
    },
{
    ol::run_admissible(eq,lib,programs(actor)(a.current[actor].unwrap()),a.state,actor);
    if let g::Node::Child {child,..}=programs(actor)(a.current[actor].unwrap()) {
        p::empty_insertion(a.state,g::entry(lib,programs,a,actor).landed.state,child,ISet::full());
        assert(fu::entry_pair(lib,programs,g::entry(lib,programs,a,actor),owner).forward =~= fu::identity());
        assert(fu::entry_pair(lib,programs,g::entry(lib,programs,a,actor),owner).inverse =~= fu::identity());
    }
}

/// The actual foreign child record occupies the catalogue, but contributes no
/// own forward or inverse; all-table identity is proved for the real landing.
pub proof fn synchronized_landing<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::well_formed(lib,programs,target),transport::related(eq,a,target,offset,owner),
        own::separated(a.state,owner),g::step(lib,programs,a,z,actor,rule),g::landing(a,z,rule),guard(programs,a,actor,owner),
        batch_state::synchronized(eq,actions,a,target),own::pinned_tokens(a.history,a.state.accumulators[owner],a.state,owner),
    ensures {
        let out=transport::advance(lib,programs,a,z,target,actor,rule,owner);let call=fu::entry_pair(lib,programs,g::entry(lib,programs,a,actor),owner);
        &&& g::step(lib,programs,target,out,actor,rule) && g::well_formed(lib,programs,out) && transport::related(eq,z,out,offset,owner)
        &&& own::separated(z.state,owner) && g::well_formed(lib,programs,z)
        &&& batch_state::synchronized(eq,actions.push(fu::Action::Forward {call}),z,out)
        &&& own::pinned_tokens(z.history,z.state.accumulators[owner],z.state,owner)
        &&& sh::receipt_word(z.history,z.state.accumulators[owner])==sh::receipt_word(a.history,a.state.accumulators[owner])
    },
{
    landing_transport(eq,lib,programs,a,z,target,offset,owner,actor,rule);ol::frame(eq,lib,programs,a,z,actor,rule);
    source_landing(eq,lib,programs,a,z,actor,rule,owner);owner_pins(a,z,owner);
    call_projects(eq,lib,programs,a,actor,owner);
    let call=fu::entry_pair(lib,programs,g::entry(lib,programs,a,actor),owner);assert(!call.own);batch_state::own_words_push(actions,fu::Action::Forward {call});
}

/// Foreign records remain in provenance without entering the owner's LIFO
/// value word. This is a journal equation, not a statement about replay states.
pub proof fn foreign_word<S>(actions:Seq<fu::Action<S>>,action:fu::Action<S>)
    requires match action {fu::Action::Forward {call}=>!call.own,fu::Action::Identity=>true,_=>false},
    ensures crate::strict_journal::journal(fu::events(actions.push(action)))==crate::strict_journal::journal(fu::events(actions)),
{
    let next=actions.push(action);assert(next.drop_last() =~= actions);assert(next.last()==action);
    let after=fu::events(next);assert(after =~= fu::events(actions).push(fu::event(fu::catalog(actions),action)));
    assert(after.drop_last() =~= fu::events(actions));assert(!after.last().own);
}

pub open spec fn child_tokens<U,I>(entries:Seq<g::Entry<U,I>>,tokens:Seq<nat>,actor:usize)->bool {
    forall|i:int| #![trigger tokens[i]] 0<=i<tokens.len() ==> tokens[i]<entries.len() && match entries[tokens[i] as int].landed.receipt {g::Receipt::Child {actor:who,..}=>who==actor,_=>false}
}

/// Live-journal retention proves child inverses defined before a source
/// Unload is assumed. Each retirement preserves all remaining captured names.
pub proof fn retained_children_defined<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,tokens:Seq<nat>,actor:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),s::registered(a.state,actor),child_tokens(a.history,tokens,actor),
        forall|i:int|0<=i<tokens.len() ==> a.state.accumulators[actor].contains(tokens[i]),
    ensures g::restore(a.history,tokens,a.state,actor).is_some(),
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let token=tokens.last();assert(token<a.history.len());assert(a.state.accumulators[actor].contains(token));
        if let g::Receipt::Child {actor:who,child}=a.history[token as int].landed.receipt {
            assert(g::kind(a.history)(token)==Some(child));assert(s::registered(a.state,child));
            let next=with_state(a,g::undo(a.history[token as int].landed.receipt,a.state).unwrap());
            ch::concrete_child_retirement(a.state,child);assert(g::step(lib,programs,a,next,child,r::Rule::Retire));
            ol::configuration_preservation(eq,lib,programs,a,next,child,r::Rule::Retire);
            assert(child_tokens(next.history,tokens.drop_last(),actor)) by {assert forall|i:int| #![trigger tokens.drop_last()[i]] 0<=i<tokens.drop_last().len() implies tokens.drop_last()[i]<next.history.len()
                && match next.history[tokens.drop_last()[i] as int].landed.receipt {g::Receipt::Child {actor:who,..}=>who==actor,_=>false} by {assert(tokens.drop_last()[i]==tokens[i]);}}
            retained_children_defined(eq,lib,programs,next,tokens.drop_last(),actor);
        }
    }
}

/// Value-neutral control steps after a child entry do not need the old Table
/// history profile. Begin is excluded here because it can replace commitment.
pub proof fn control_transport<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::well_formed(lib,programs,target),transport::related(eq,a,target,offset,owner),own::separated(a.state,owner),
        g::step(lib,programs,a,z,actor,rule),!g::landing(a,z,rule),rule==r::Rule::Retire || rule==r::Rule::Leave || rule==r::Rule::Divert,
        batch_state::synchronized(eq,actions,a,target),own::pinned_tokens(a.history,a.state.accumulators[owner],a.state,owner),
    ensures {
        let out=transport::advance(lib,programs,a,z,target,actor,rule,owner);
        &&& (sh::keep(actor,rule,owner) ==> g::step(lib,programs,target,out,actor,rule))
        &&& g::well_formed(lib,programs,z) && g::well_formed(lib,programs,out) && transport::related(eq,z,out,offset,owner) && own::separated(z.state,owner)
        &&& batch_state::synchronized(eq,actions.push(fu::Action::Identity),z,out)
        &&& own::pinned_tokens(z.history,z.state.accumulators[owner],z.state,owner)
        &&& sh::receipt_word(z.history,z.state.accumulators[owner])==sh::receipt_word(a.history,a.state.accumulators[owner])
    },
{
    ol::configuration_preservation(eq,lib,programs,a,z,actor,rule);ol::frame(eq,lib,programs,a,z,actor,rule);
    own::interface_frame(eq,lib,programs,a,z,actor,rule,owner);sh::source_domains(eq,lib,programs,a,z,actor,rule);
    transport::control_transport(eq,lib,programs,a,z,target,offset,owner,actor,rule);owner_pins(a,z,owner);
    p::unique_owner(a.state);p::unique_owner(z.state);assert(p::bindings_equal(a.state,z.state));p::projection_equal(a.state,z.state,ISet::full());
    batch_state::own_words_push(actions,fu::Action::Identity);
}

// Check the concrete child inverse before composing its transport contracts.
proof fn child_inverse_state<U>(a:s::State<U>,actor:usize,child:usize)
    ensures g::undo(g::Receipt::<U>::Child {actor,child},a)==if s::registered(a,child) {
        Some(s::with_control(a,crate::global::retire_fiber(a.control,child)))
    } else {None},
{ }

/// One genuine captured-child retirement is transported through the common
/// registry. Retirement may also affect the deleted owner's own retired bit.
pub proof fn inverse_transport<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,target:g::Configuration<U,I>,offset:nat,owner:usize,actor:usize,child:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::well_formed(lib,programs,target),transport::related(eq,a,target,offset,owner),own::separated(a.state,owner),
        g::undo(g::Receipt::<U>::Child {actor,child},a.state).is_some(),
    ensures {
        let left=with_state(a,g::undo(g::Receipt::<U>::Child {actor,child},a.state).unwrap());let right=g::undo(g::Receipt::<U>::Child {actor,child},target.state);
        let out=with_state(target,right.unwrap());
        &&& right.is_some() && g::well_formed(lib,programs,left) && g::well_formed(lib,programs,out)
        &&& transport::related(eq,left,out,offset,owner) && own::separated(left.state,owner)
        &&& left.state.tables==a.state.tables && out.state.tables==target.state.tables
        &&& p::project(left.state,ISet::full())==p::project(a.state,ISet::full()) && p::project(out.state,ISet::full())==p::project(target.state,ISet::full())
        &&& left.history==a.history && left.state.accumulators==a.state.accumulators
        &&& forall|n:usize|s::registered(a.state,n) ==> r::interface_same(a.state.control.fibers[n],left.state.control.fibers[n]) && a.state.control.fibers[n].committed==left.state.control.fibers[n].committed
    },
{
    hide(og::primitive_theory);hide(g::undo);
    child_inverse_state(a.state,actor,child);child_inverse_state(target.state,actor,child);
    let left=with_state(a,g::undo(g::Receipt::<U>::Child {actor,child},a.state).unwrap());
    ch::concrete_child_retirement(a.state,child);assert(g::step(lib,programs,a,left,child,r::Rule::Retire));
    ol::configuration_preservation(eq,lib,programs,a,left,child,r::Rule::Retire);ol::frame(eq,lib,programs,a,left,child,r::Rule::Retire);
    own::interface_frame(eq,lib,programs,a,left,child,r::Rule::Retire,owner);
    transport::control_transport(eq,lib,programs,a,left,target,offset,owner,child,r::Rule::Retire);
    p::unique_owner(a.state);p::unique_owner(left.state);assert(p::bindings_equal(a.state,left.state));p::projection_equal(a.state,left.state,ISet::full());
}

/// Restore a child-only journal of any age using the target's own mapped tokens.
/// The whole source restore is a fact of the real source Unload, not a target
/// enabledness assumption. Each target captured identity is proved registered.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn restore_children<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,target:g::Configuration<U,I>,tokens:Seq<nat>,offset:nat,owner:usize,actor:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::well_formed(lib,programs,target),transport::related(eq,a,target,offset,owner),own::separated(a.state,owner),actor!=owner,
        child_tokens(a.history,tokens,actor),g::restore(a.history,tokens,a.state,actor).is_some(),
    ensures {
        let left=with_state(a,g::restore(a.history,tokens,a.state,actor).unwrap());let right=g::restore(target.history,history::rename(a.history,offset,owner,tokens),target.state,actor);let out=with_state(target,right.unwrap());
        &&& right.is_some() && g::well_formed(lib,programs,left) && g::well_formed(lib,programs,out)
        &&& transport::related(eq,left,out,offset,owner) && own::separated(left.state,owner)
        &&& left.state.tables==a.state.tables && out.state.tables==target.state.tables
        &&& p::project(left.state,ISet::full())==p::project(a.state,ISet::full()) && p::project(out.state,ISet::full())==p::project(target.state,ISet::full())
        &&& left.state.accumulators==a.state.accumulators && out.state.accumulators==target.state.accumulators
        &&& left.state.control.fibers.dom()==a.state.control.fibers.dom() && out.state.control.fibers.dom()==target.state.control.fibers.dom()
        &&& forall|n:usize|s::registered(a.state,n) ==> r::interface_same(a.state.control.fibers[n],left.state.control.fibers[n]) && a.state.control.fibers[n].committed==left.state.control.fibers[n].committed
    },
    decreases tokens.len(),
{
    history::rename_laws(a.history,offset,owner,tokens,0);
    if tokens.len()>0 {
        let token=tokens.last();let mapped=history::index(a.history,offset,owner,token);let receipt=a.history[token as int].landed.receipt;
        assert(token<a.history.len());assert(g::owner(receipt)==actor);
        if token<offset {reveal(history::index);assert(mapped==token);assert(target.history[mapped as int]==a.history[token as int]);}
        else {assert(obs::receipt_related(eq,receipt,target.history[mapped as int].landed.receipt));}
        assert(mapped<target.history.len());assert(receipt==target.history[mapped as int].landed.receipt);
        if let g::Receipt::Child {actor:who,child}=receipt {
            inverse_transport(eq,lib,programs,a,target,offset,owner,actor,child);
            let left=with_state(a,g::undo(receipt,a.state).unwrap());let right=with_state(target,g::undo(receipt,target.state).unwrap());
            assert(child_tokens(left.history,tokens.drop_last(),actor)) by {assert forall|i:int| #![trigger tokens.drop_last()[i]] 0<=i<tokens.drop_last().len() implies tokens.drop_last()[i]<left.history.len()
                && match left.history[tokens.drop_last()[i] as int].landed.receipt {g::Receipt::Child {actor:who,..}=>who==actor,_=>false} by {assert(tokens.drop_last()[i]==tokens[i]);}}
            restore_children(eq,lib,programs,left,right,tokens.drop_last(),offset,owner,actor);
            assert forall|n:usize|s::registered(a.state,n) implies r::interface_same(a.state.control.fibers[n],g::restore(a.history,tokens,a.state,actor).unwrap().control.fibers[n])
                && a.state.control.fibers[n].committed==g::restore(a.history,tokens,a.state,actor).unwrap().control.fibers[n].committed by {assert(s::registered(left.state,n));}
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn unload_transport<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,actor:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::well_formed(lib,programs,target),transport::related(eq,a,target,offset,owner),own::separated(a.state,owner),actor!=owner,
        g::step(lib,programs,a,z,actor,r::Rule::Unload),child_tokens(a.history,a.state.accumulators[actor],actor),
        batch_state::synchronized(eq,actions,a,target),own::pinned_tokens(a.history,a.state.accumulators[owner],a.state,owner),
    ensures {
        let out=g::unload(target,actor);
        &&& g::step(lib,programs,target,out,actor,r::Rule::Unload) && g::well_formed(lib,programs,out) && transport::related(eq,z,out,offset,owner)
        &&& g::well_formed(lib,programs,z) && own::separated(z.state,owner)
        &&& batch_state::synchronized(eq,actions.push(fu::Action::Identity),z,out)
        &&& own::pinned_tokens(z.history,z.state.accumulators[owner],z.state,owner)
        &&& sh::receipt_word(z.history,z.state.accumulators[owner])==sh::receipt_word(a.history,a.state.accumulators[owner])
    },
{
    let tokens=a.state.accumulators[actor];restore_children(eq,lib,programs,a,target,tokens,offset,owner,actor);
    let restored=g::restore(a.history,tokens,a.state,actor).unwrap();let kept=g::restore(target.history,history::rename(a.history,offset,owner,tokens),target.state,actor).unwrap();
    let left=with_state(a,restored);let right=with_state(target,kept);let out=g::unload(target,actor);
    transport::no_users(a,target,owner,actor);assert(g::step(lib,programs,target,out,actor,r::Rule::Unload));
    ol::configuration_preservation(eq,lib,programs,a,z,actor,r::Rule::Unload);ol::frame(eq,lib,programs,a,z,actor,r::Rule::Unload);
    ol::configuration_preservation(eq,lib,programs,target,out,actor,r::Rule::Unload);ol::frame(eq,lib,programs,target,out,actor,r::Rule::Unload);
    own::interface_frame(eq,lib,programs,a,z,actor,r::Rule::Unload,owner);owner_pins(a,z,owner);
    assert forall|n:usize|s::registered(z.state,n) && n!=owner implies {
        &&& z.state.tables[n].dom()==out.state.tables[n].dom()
        &&& z.state.control.fibers[n]==out.state.control.fibers[n] && z.current[n]==out.current[n]
    } by {assert(s::registered(left.state,n));}
    assert forall|n:usize|s::registered(z.state,n) && n!=owner implies out.state.accumulators[n]==history::rename(z.history,offset,owner,z.state.accumulators[n]) by {
        assert(s::registered(a.state,n));if n==actor {history::rename_laws(a.history,offset,owner,Seq::empty(),0);}
    }
    p::unique_owner(restored);p::unique_owner(kept);
    p::lifecycle_edit(restored,actor,Phase::Inactive,ISet::empty(),None,Seq::empty(),ISet::full());
    p::lifecycle_edit(kept,actor,Phase::Inactive,ISet::empty(),None,Seq::empty(),ISet::full());
    batch_state::own_words_push(actions,fu::Action::Identity);
}

} // verus!
