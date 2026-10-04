//! A partial context-mediated interpreter on the full registry state.
//!
//! Dependency operations resolve the installed committed provider, not the
//! current publication. Every successful stage returns its actual inverse;
//! missing actors, bindings and operation/inverse domains remain failures.
use crate::{mediated as grammar, semantics as full, Port};
#[cfg(verus_keep_ghost)]
use crate::{preservation as inv, projection, refinement as control, Binding, Phase};
use vstd::prelude::*;

verus! {

#[verifier::reject_recursive_types(V)]
pub enum Inverse<V> {
    Unit,
    Operation { provider: usize, key: Port, undo: grammar::PartialMap<V> },
    Provision { key: Port },
}

#[verifier::reject_recursive_types(V)]
pub struct Receipt<V> { pub actor: usize, pub inverse: Inverse<V> }
#[verifier::reject_recursive_types(V)]
pub struct Landed<V> { pub state: full::State<V>, pub receipt: Receipt<V>, pub next: Option<nat> }

pub open spec fn names_key(b: Binding, key: Port) -> bool { b.key == key.key && b.realm == key.realm }

/// A dependency is resolved only through the episode's installed commitment.
/// A provision belongs to the actor even before it becomes publicly Active.
pub open spec fn resolve<V>(a: full::State<V>, actor: usize, key: Port) -> Option<usize> {
    if !full::registered(a, actor) { None }
    else if a.control.fibers[actor].provisions.contains(key) { Some(actor) }
    else if a.control.fibers[actor].dependencies.contains(key)
        && exists|b: Binding| a.control.fibers[actor].committed.contains(b) && names_key(b, key) {
        Some((choose|b: Binding| a.control.fibers[actor].committed.contains(b) && names_key(b, key)).provider)
    } else { None }
}

pub proof fn resolution_sound<V>(a: full::State<V>, actor: usize, key: Port)
    requires inv::well_formed(a), resolve(a, actor, key).is_some(),
    ensures {
        let provider = resolve(a, actor, key).unwrap();
        &&& full::registered(a, actor) && full::registered(a, provider)
        &&& a.control.fibers[provider].provisions.contains(key)
        &&& (provider == actor || a.control.fibers[actor].dependencies.contains(key))
        &&& (provider != actor ==> a.control.fibers[actor].committed.contains(Binding {key:key.key,realm:key.realm,provider}))
    },
{
    if !a.control.fibers[actor].provisions.contains(key) {
        let b = choose|b: Binding| a.control.fibers[actor].committed.contains(b) && names_key(b, key);
        assert(a.control.fibers[actor].committed.contains(b));
        assert(b == Binding {key:key.key,realm:key.realm,provider:b.provider});
    }
}

/// The node's syntax and declarations supply confinement. No `forward_map`
/// or final-state invariant is supplied by this interpreter's caller.
pub open spec fn run<V, O>(node: grammar::Node<Port, V, O>, a: full::State<V>, actor: usize) -> Option<Landed<V>> {
    if !full::registered(a, actor) { None }
    else { match node {
        grammar::Node::Unit => Some(Landed { state:a, receipt:Receipt {actor,inverse:Inverse::Unit}, next:None }),
        grammar::Node::Operation { key, operation, select } => match resolve(a, actor, key) {
            None => None,
            Some(provider) => {
                if !full::registered(a, provider) || !a.tables[provider].dom().contains(key) { None }
                else { match operation(a.tables[provider][key]) {
                    None => None,
                    Some(y) => Some(Landed {state:projection::update_slot(a,provider,key,Some(y.value)),
                        receipt:Receipt {actor,inverse:Inverse::Operation {provider,key,undo:y.undo}}, next:select(y.outcome)}),
                } }
            },
        },
        grammar::Node::Provision {key,value,next} => {
            if !a.control.fibers[actor].provisions.contains(key) || a.tables[actor].dom().contains(key) { None }
            else {Some(Landed {state:projection::update_slot(a,actor,key,Some(value)),
                receipt:Receipt {actor,inverse:Inverse::Provision {key}},next})}
        },
    } }
}

/// Recovery retains its captured provider and verifies that the current
/// commitment still resolves that key there. It never redirects to a replacement
/// provider. Receipt itself has no generation; the execution journal supplies
/// episode ownership by discarding live accumulator tokens at Unload.
pub open spec fn undo<V>(receipt: Receipt<V>, a: full::State<V>) -> Option<full::State<V>> {
    let actor = receipt.actor;
    if !full::registered(a, actor) { None }
    else { match receipt.inverse {
        Inverse::Unit => Some(a),
        Inverse::Operation {provider,key,undo} => {
            if resolve(a,actor,key) != Some(provider) || !full::registered(a,provider)
                || !a.tables[provider].dom().contains(key) {None}
            else {match undo(a.tables[provider][key]) {
                None => None, Some(value) => Some(projection::update_slot(a,provider,key,Some(value))),
            }}
        },
        Inverse::Provision {key} => {
            if !a.control.fibers[actor].provisions.contains(key) || !a.tables[actor].dom().contains(key) {None}
            else {Some(projection::update_slot(a,actor,key,None))}
        },
    } }
}

pub proof fn run_preservation<V, O>(node: grammar::Node<Port, V, O>, a: full::State<V>, actor: usize)
    requires inv::well_formed(a), run(node,a,actor).is_some(),
    ensures {
        let out=run(node,a,actor).unwrap();
        &&& out.receipt.actor==actor && full::registered(a,actor)
        &&& inv::table_map(a,out.state,actor) && inv::well_formed(out.state)
        &&& out.state.control==a.control && out.state.effects==a.effects
        &&& out.state.iterators==a.iterators && out.state.accumulators==a.accumulators
    },
{
    match node {
        grammar::Node::Unit => { },
        grammar::Node::Operation {key,operation,..} => {
            resolution_sound(a,actor,key);
            let provider=resolve(a,actor,key).unwrap();
            let y=operation(a.tables[provider][key]).unwrap();
            projection::update_slot_confined(a,actor,provider,key,Some(y.value));
        },
        grammar::Node::Provision {key,value,..} => {
            projection::update_slot_confined(a,actor,actor,key,Some(value));
        },
    }
}

pub proof fn undo_preservation<V>(receipt:Receipt<V>,a:full::State<V>)
    requires inv::well_formed(a),undo(receipt,a).is_some(),
    ensures inv::table_map(a,undo(receipt,a).unwrap(),receipt.actor),inv::well_formed(undo(receipt,a).unwrap()),
        full::registered(a,receipt.actor),undo(receipt,a).unwrap().control==a.control,
        undo(receipt,a).unwrap().effects==a.effects,undo(receipt,a).unwrap().iterators==a.iterators,
        undo(receipt,a).unwrap().accumulators==a.accumulators,
{
    match receipt.inverse {
        Inverse::Unit => { },
        Inverse::Operation {provider,key,undo:inverse} => {
            resolution_sound(a,receipt.actor,key);
            projection::update_slot_confined(a,receipt.actor,provider,key,Some(inverse(a.tables[provider][key]).unwrap()));
        },
        Inverse::Provision {key} => {projection::update_slot_confined(a,receipt.actor,receipt.actor,key,None);},
    }
}

pub proof fn immediate_recovery<V, O>(eq:spec_fn(Port,V,V)->bool,allowed:grammar::Allowed<Port,V,O>,
    program:grammar::Program<Port,V,O>,id:nat,a:full::State<V>,actor:usize)
    requires inv::well_formed(a),full::registered(a,actor),grammar::primitive_theory(eq,allowed),
        grammar::member(program,allowed,a.control.fibers[actor].dependencies.union(a.control.fibers[actor].provisions),
            a.control.fibers[actor].provisions,id),run(program(id),a,actor).is_some(),
    ensures {
        let out=run(program(id),a,actor).unwrap();
        &&& undo(out.receipt,out.state)==Some(a)
        &&& out.next.is_some() ==> grammar::member(program,allowed,a.control.fibers[actor].dependencies.union(a.control.fibers[actor].provisions),
            a.control.fibers[actor].provisions,out.next.unwrap())
    },
{
    let keys=a.control.fibers[actor].dependencies.union(a.control.fibers[actor].provisions);
    grammar::member_permitted(program,allowed,keys,a.control.fibers[actor].provisions,id);
    grammar::context_mediated_admissible(eq,program,allowed,keys,a.control.fibers[actor].provisions,id);
    run_preservation(program(id),a,actor);
    let out=run(program(id),a,actor).unwrap();
    match program(id) {
        grammar::Node::Unit => { },
        grammar::Node::Operation {key,operation,select} => {
            resolution_sound(a,actor,key);
            let provider=resolve(a,actor,key).unwrap();
            let y=operation(a.tables[provider][key]).unwrap();
            assert(grammar::operation_admissible(|x:V,y:V|eq(key,x,y),operation));
            assert((y.undo)(y.value)==Some(a.tables[provider][key]));
            assert(resolve(out.state,actor,key)==Some(provider));
            projection::operation_stage_lift(a,actor,provider,key,operation,select);
        },
        grammar::Node::Provision {key,value,next} => {
            projection::provision_stage_lift::<V,O>(a,actor,key,value,next);
        },
    }
}

pub type Programs<V,O> = spec_fn(usize)->grammar::Program<Port,V,O>;

/// A record stores the exact result that appended its token. Equality is
/// checked against the actual interpreter application, not supplied separately
/// as a desired rollback history.
#[verifier::reject_recursive_types(V)]
pub struct Entry<V> {
    pub input:full::State<V>,pub iterator:nat,pub landed:Landed<V>,
}

#[verifier::reject_recursive_types(V)]
pub struct Configuration<V> { pub state:full::State<V>,pub history:Seq<Entry<V>> }

pub open spec fn entry<V,O>(programs:Programs<V,O>,a:full::State<V>,actor:usize) -> Entry<V> {
    let iterator=a.iterators[actor].unwrap();
    Entry {input:a,iterator,landed:run(programs(actor)(iterator),a,actor).unwrap()}
}

/// The key of a mathematical interpreter application includes its complete
/// input state. Repeated applications use the same inverse identity even when
/// they occur in different episodes; every occurrence is still recorded.
pub open spec fn same_call<V>(e:Entry<V>,actor:usize,id:nat,input:full::State<V>) -> bool {
    e.landed.receipt.actor==actor && e.iterator==id && e.input==input
}

/// Return the earliest matching index, or the history length if absent.
pub open spec fn first_call<V>(history:Seq<Entry<V>>,actor:usize,id:nat,input:full::State<V>) -> nat
    decreases history.len(),
{
    if history.len()==0 {0}
    else {
        let previous=first_call(history.drop_last(),actor,id,input);
        if previous<history.len()-1 {previous}
        else if same_call(history.last(),actor,id,input) {(history.len()-1) as nat}
        else {history.len()}
    }
}

pub proof fn first_call_properties<V>(history:Seq<Entry<V>>,actor:usize,id:nat,input:full::State<V>)
    ensures first_call(history,actor,id,input)<=history.len(),
        first_call(history,actor,id,input)<history.len() ==> same_call(history[first_call(history,actor,id,input) as int],actor,id,input),
        forall|i:int| 0<=i<first_call(history,actor,id,input) ==> !same_call(#[trigger] history[i],actor,id,input),
    decreases history.len(),
{
    if history.len()>0 {
        let prefix=history.drop_last();
        first_call_properties(prefix,actor,id,input);
        let previous=first_call(prefix,actor,id,input);
        let chosen=first_call(history,actor,id,input);
        if chosen<history.len() && chosen<prefix.len() {assert(history[chosen as int]==prefix[chosen as int]);}
        assert forall|i:int| 0<=i<chosen implies !same_call(#[trigger] history[i],actor,id,input) by {
            if i<prefix.len() {assert(prefix[i]==history[i]);}
            else {assert(i==history.len()-1);}
        }
    }
}

pub open spec fn call_token<V>(a:Configuration<V>,actor:usize) -> nat {
    first_call(a.history,actor,a.state.iterators[actor].unwrap(),a.state)
}

pub proof fn first_call_append<V>(history:Seq<Entry<V>>,e:Entry<V>,actor:usize,id:nat,input:full::State<V>)
    requires same_call(e,actor,id,input),
    ensures first_call(history.push(e),actor,id,input)==first_call(history,actor,id,input),
        first_call(history,actor,id,input)<history.push(e).len(),
        same_call(history.push(e)[first_call(history,actor,id,input) as int],actor,id,input),
{
    first_call_properties(history,actor,id,input);
    assert(history.push(e).drop_last()==history);
    first_call_properties(history.push(e),actor,id,input);
}

pub open spec fn tokens_valid<V>(a:Configuration<V>) -> bool {
    forall|actor:usize,i:int| #![trigger a.state.accumulators[actor][i]] full::registered(a.state,actor) && 0<=i<a.state.accumulators[actor].len() ==> {
        let token=a.state.accumulators[actor][i];
        &&& token<a.history.len()
        &&& a.history[token as int].landed.receipt.actor==actor
    }
}

pub open spec fn history_sound<V,O>(programs:Programs<V,O>,history:Seq<Entry<V>>) -> bool {
    forall|i:int| #![trigger history[i]] 0<=i<history.len() ==> {
        let e=history[i];
        &&& run(programs(e.landed.receipt.actor)(e.iterator),e.input,e.landed.receipt.actor)==Some(e.landed)
        &&& undo(e.landed.receipt,e.landed.state)==Some(e.input)
    }
}

pub open spec fn component_member<V,O>(programs:Programs<V,O>,allowed:grammar::Allowed<Port,V,O>,a:full::State<V>,actor:usize,id:nat) -> bool {
    grammar::member(programs(actor),allowed,a.control.fibers[actor].dependencies.union(a.control.fibers[actor].provisions),
        a.control.fibers[actor].provisions,id)
}

pub open spec fn components_typed<V,O>(programs:Programs<V,O>,allowed:grammar::Allowed<Port,V,O>,a:full::State<V>) -> bool {
    forall|actor:usize| full::registered(a,actor) ==> {
        &&& component_member(programs,allowed,a,actor,a.effects[actor])
        &&& (a.iterators[actor].is_some() ==> component_member(programs,allowed,a,actor,a.iterators[actor].unwrap()))
    }
}

pub open spec fn well_formed<V,O>(programs:Programs<V,O>,allowed:grammar::Allowed<Port,V,O>,a:Configuration<V>) -> bool {
    inv::well_formed(a.state) && tokens_valid(a) && history_sound(programs,a.history) && components_typed(programs,allowed,a.state)
}

/// Restoration evaluates recorded inverses in the accumulator's reverse order.
/// A missing token, another actor's token, absent binding or inverse failure
/// returns None and cannot become a successful L-Unload transition.
pub open spec fn restore<V>(history:Seq<Entry<V>>,tokens:Seq<nat>,a:full::State<V>,actor:usize) -> Option<full::State<V>>
    decreases tokens.len(),
{
    if tokens.len()==0 {Some(a)}
    else if tokens.last()>=history.len() || history[tokens.last() as int].landed.receipt.actor!=actor {None}
    else {match undo(history[tokens.last() as int].landed.receipt,a) {
        None=>None,Some(next)=>restore(history,tokens.drop_last(),next,actor),
    }}
}

pub proof fn restore_preservation<V>(history:Seq<Entry<V>>,tokens:Seq<nat>,a:full::State<V>,actor:usize)
    requires inv::well_formed(a),restore(history,tokens,a,actor).is_some(),
    ensures inv::well_formed(restore(history,tokens,a,actor).unwrap()),
        restore(history,tokens,a,actor).unwrap().control==a.control,
        restore(history,tokens,a,actor).unwrap().effects==a.effects,
        restore(history,tokens,a,actor).unwrap().iterators==a.iterators,
        restore(history,tokens,a,actor).unwrap().accumulators==a.accumulators,
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let receipt=history[tokens.last() as int].landed.receipt;
        undo_preservation(receipt,a);
        restore_preservation(history,tokens.drop_last(),undo(receipt,a).unwrap(),actor);
    }
}

pub open spec fn land<V,O>(programs:Programs<V,O>,a:Configuration<V>,actor:usize,phase:Phase) -> Configuration<V> {
    let recorded=entry(programs,a.state,actor);
    let next=if phase==Phase::Loading {recorded.landed.next} else {None};
    Configuration {state:full::edit(recorded.landed.state,actor,phase,a.state.control.fibers[actor].committed,
        next,a.state.accumulators[actor].push(call_token(a,actor))),history:a.history.push(recorded)}
}

/// The nine paper rules instantiated by the partial grammar interpreter.
/// Insertion supplies only its well-typed component and concrete initialized
/// fields. Effect admissibility is derived by the preservation theorem below.
pub open spec fn step<V,O>(programs:Programs<V,O>,allowed:grammar::Allowed<Port,V,O>,a:Configuration<V>,z:Configuration<V>,actor:usize,rule:control::Rule) -> bool {
    let s=a.state;
    let t=z.state;
    match rule {
        control::Rule::Insert => inv::insert_map(s,t,actor) && z.history==a.history
            && component_member(programs,allowed,t,actor,t.effects[actor]),
        control::Rule::Retire => full::child_retire(s,t,actor) && z.history==a.history,
        control::Rule::Remove => control::step(s.control,t.control,actor,rule) && s.tables[actor].is_empty()
            && t==full::erase(s,actor) && z.history==a.history,
        control::Rule::Begin => full::registered(s,actor) && s.control.fibers[actor].phase==Phase::Inactive
            && full::target(s,actor,t.control.fibers[actor].committed)
            && t==full::edit(s,actor,Phase::Loading,t.control.fibers[actor].committed,Some(s.effects[actor]),Seq::empty())
            && z.history==a.history,
        control::Rule::Iter | control::Rule::Finish => {
            let result=run(programs(actor)(s.iterators[actor].unwrap()),s,actor);
            &&& full::registered(s,actor) && s.control.fibers[actor].phase==Phase::Loading && s.iterators[actor].is_some()
            &&& full::coherent(s,actor) && result.is_some()
            &&& (rule==control::Rule::Iter)==result.unwrap().next.is_some()
            &&& z==land(programs,a,actor,if rule==control::Rule::Iter {Phase::Loading} else {Phase::Active})
        },
        control::Rule::Divert => {
            &&& full::registered(s,actor) && s.control.fibers[actor].phase==Phase::Loading && s.iterators[actor].is_some()
            &&& !full::coherent(s,actor)
            &&& ((t==full::edit(s,actor,Phase::Unloading,s.control.fibers[actor].committed,None,s.accumulators[actor]) && z.history==a.history)
                || (run(programs(actor)(s.iterators[actor].unwrap()),s,actor).is_some() && z==land(programs,a,actor,Phase::Unloading)))
        },
        control::Rule::Leave => full::registered(s,actor) && s.control.fibers[actor].phase==Phase::Active && !full::coherent(s,actor)
            && t==full::edit(s,actor,Phase::Unloading,s.control.fibers[actor].committed,None,s.accumulators[actor]) && z.history==a.history,
        control::Rule::Unload => full::registered(s,actor) && s.control.fibers[actor].phase==Phase::Unloading
            && !control::relied(s.control,actor) && restore(a.history,s.accumulators[actor],s,actor).is_some()
            && t==full::edit(restore(a.history,s.accumulators[actor],s,actor).unwrap(),actor,Phase::Inactive,ISet::empty(),None,Seq::empty())
            && z.history==a.history,
        _=>false,
    }
}

pub proof fn removal_preservation<V>(a:full::State<V>,n:usize)
    requires inv::well_formed(a),control::step(a.control,full::erase(a,n).control,n,control::Rule::Remove),
    ensures inv::well_formed(full::erase(a,n)),
{
    let z=full::erase(a,n);
    inv::control_preservation(a.control,z.control,n,control::Rule::Remove);
    assert forall|m:usize| full::registered(z,m) implies {
        &&& z.tables[m].dom().subset_of(z.control.fibers[m].provisions)
        &&& (z.control.fibers[m].phase==Phase::Inactive ==> z.iterators[m].is_none() && z.accumulators[m].len()==0 && z.control.fibers[m].committed.is_empty())
        &&& (z.control.fibers[m].phase==Phase::Loading ==> z.iterators[m].is_some())
        &&& (z.control.fibers[m].phase==Phase::Active || z.control.fibers[m].phase==Phase::Unloading ==> z.iterators[m].is_none())
    } by {assert(m!=n);assert(full::registered(a,m));}
}

pub proof fn unloading_preservation<V>(history:Seq<Entry<V>>,a:full::State<V>,actor:usize)
    requires inv::well_formed(a),full::registered(a,actor),a.control.fibers[actor].phase==Phase::Unloading,
        !control::relied(a.control,actor),restore(history,a.accumulators[actor],a,actor).is_some(),
    ensures inv::well_formed(full::edit(restore(history,a.accumulators[actor],a,actor).unwrap(),actor,Phase::Inactive,ISet::empty(),None,Seq::empty())),
{
    restore_preservation(history,a.accumulators[actor],a,actor);
    let context=restore(history,a.accumulators[actor],a,actor).unwrap();
    let z=full::edit(context,actor,Phase::Inactive,ISet::empty(),None,Seq::empty());
    assert(control::frame(context.control,z.control,actor)) by {
        assert forall|n:usize| n!=actor implies control::registered(context.control,n)==control::registered(z.control,n)
            && (control::registered(context.control,n) ==> context.control.fibers[n]==z.control.fibers[n]) by { }
    }
    assert(control::step(context.control,z.control,actor,control::Rule::Unload));
    inv::control_preservation(context.control,z.control,actor,control::Rule::Unload);
    inv::shaped_edit(context,actor,Phase::Inactive,ISet::empty(),None,Seq::empty());
}

pub proof fn state_preservation<V,O>(programs:Programs<V,O>,allowed:grammar::Allowed<Port,V,O>,a:Configuration<V>,z:Configuration<V>,actor:usize,rule:control::Rule)
    requires inv::well_formed(a.state),step(programs,allowed,a,z,actor,rule),
    ensures inv::well_formed(z.state),
{
    let s=a.state;let t=z.state;
    match rule {
        control::Rule::Insert=>{inv::insert_preservation(s,t,actor);},
        control::Rule::Retire=>{inv::retire_preservation(s,t,actor);},
        control::Rule::Remove=>{removal_preservation(s,actor);},
        control::Rule::Begin=>{inv::begin_preservation(s,t,actor);},
        control::Rule::Iter | control::Rule::Finish=>{
            let node=programs(actor)(s.iterators[actor].unwrap());
            run_preservation(node,s,actor);
            let out=run(node,s,actor).unwrap();
            if rule==control::Rule::Finish {inv::finish_preservation(s,out.state,actor,s.accumulators[actor].push(call_token(a,actor)));}
            else {
                inv::shaped_edit(out.state,actor,Phase::Loading,s.control.fibers[actor].committed,out.next,s.accumulators[actor].push(call_token(a,actor)));
                assert(t.control.fibers =~= s.control.fibers) by {
                    assert forall|n:usize| t.control.fibers.dom().contains(n) implies t.control.fibers[n]==s.control.fibers[n] by { }
                }
            }
        },
        control::Rule::Divert=>{
            if t==full::edit(s,actor,Phase::Unloading,s.control.fibers[actor].committed,None,s.accumulators[actor]) && z.history==a.history {
                inv::unloading_edit_preservation(s,actor,s.accumulators[actor]);
            } else {
                let node=programs(actor)(s.iterators[actor].unwrap());
                run_preservation(node,s,actor);
                inv::unloading_edit_preservation(run(node,s,actor).unwrap().state,actor,s.accumulators[actor].push(call_token(a,actor)));
            }
        },
        control::Rule::Leave=>{inv::unloading_edit_preservation(s,actor,s.accumulators[actor]);},
        control::Rule::Unload=>{unloading_preservation(a.history,s,actor);},
        _=>{},
    }
}

pub open spec fn landing_rule<V>(a:Configuration<V>,z:Configuration<V>,rule:control::Rule) -> bool {
    rule==control::Rule::Iter || rule==control::Rule::Finish || (rule==control::Rule::Divert && z.history!=a.history)
}

/// Derive the metadata frame once from the actual interpreter and all nine
/// rules. These are conclusions, not effect/trace admissibility assumptions.
pub proof fn metadata_frame<V,O>(programs:Programs<V,O>,allowed:grammar::Allowed<Port,V,O>,a:Configuration<V>,z:Configuration<V>,actor:usize,rule:control::Rule)
    requires inv::well_formed(a.state),step(programs,allowed,a,z,actor,rule),
    ensures {
        &&& forall|n:usize| full::registered(a.state,n) && full::registered(z.state,n) ==>
            control::interface_same(a.state.control.fibers[n],z.state.control.fibers[n]) && a.state.effects[n]==z.state.effects[n]
        &&& forall|n:usize| n!=actor ==> full::registered(a.state,n)==full::registered(z.state,n)
            && (full::registered(a.state,n) ==> a.state.iterators[n]==z.state.iterators[n] && a.state.accumulators[n]==z.state.accumulators[n])
        &&& (landing_rule(a,z,rule) ==> {
            let recorded=entry(programs,a.state,actor);
            &&& run(programs(actor)(a.state.iterators[actor].unwrap()),a.state,actor).is_some()
            &&& recorded.landed.receipt.actor==actor
            &&& z.history==a.history.push(recorded)
            &&& z.state.accumulators[actor]==a.state.accumulators[actor].push(call_token(a,actor))
            &&& z.state.iterators[actor]==if rule==control::Rule::Iter {recorded.landed.next} else {None}
        })
        &&& (!landing_rule(a,z,rule) ==> z.history==a.history)
    },
{
    if landing_rule(a,z,rule) {
        run_preservation(programs(actor)(a.state.iterators[actor].unwrap()),a.state,actor);
    }
    if rule==control::Rule::Unload {restore_preservation(a.history,a.state.accumulators[actor],a.state,actor);}
    assert forall|n:usize| full::registered(a.state,n) && full::registered(z.state,n) implies
        control::interface_same(a.state.control.fibers[n],z.state.control.fibers[n]) && a.state.effects[n]==z.state.effects[n] by {
        match rule {
            control::Rule::Insert=>{assert(n!=actor);},
            control::Rule::Remove=>{assert(n!=actor);},
            _=>{},
        }
    }
    assert forall|n:usize| n!=actor implies full::registered(a.state,n)==full::registered(z.state,n)
        && (full::registered(a.state,n) ==> a.state.iterators[n]==z.state.iterators[n] && a.state.accumulators[n]==z.state.accumulators[n]) by { }
}

/// Every retained receipt was obtained from the interpreter, each live token
/// names its actor's actual receipt, and continuations stay in the grammar.
/// In particular none of these facts is postulated for intermediate states.
pub proof fn configuration_preservation<V,O>(eq:spec_fn(Port,V,V)->bool,programs:Programs<V,O>,allowed:grammar::Allowed<Port,V,O>,
    a:Configuration<V>,z:Configuration<V>,actor:usize,rule:control::Rule)
    requires grammar::primitive_theory(eq,allowed),well_formed(programs,allowed,a),step(programs,allowed,a,z,actor,rule),
    ensures well_formed(programs,allowed,z),
{
    state_preservation(programs,allowed,a,z,actor,rule);
    metadata_frame(programs,allowed,a,z,actor,rule);
    if landing_rule(a,z,rule) {
        assert(full::registered(a.state,actor));
        assert(a.state.iterators[actor].is_some());
        assert(component_member(programs,allowed,a.state,actor,a.state.iterators[actor].unwrap()));
        immediate_recovery(eq,allowed,programs(actor),a.state.iterators[actor].unwrap(),a.state,actor);
        let recorded=entry(programs,a.state,actor);
        assert(undo(recorded.landed.receipt,recorded.landed.state)==Some(recorded.input));
        assert(history_sound(programs,z.history)) by {
            assert forall|i:int| #![trigger z.history[i]] 0<=i<z.history.len() implies {
                let e=z.history[i];
                &&& run(programs(e.landed.receipt.actor)(e.iterator),e.input,e.landed.receipt.actor)==Some(e.landed)
                &&& undo(e.landed.receipt,e.landed.state)==Some(e.input)
            } by {
                if i<a.history.len() {assert(z.history[i]==a.history[i]);}
                else {assert(i==a.history.len());assert(z.history[i]==recorded);}
            }
        }
    }
    assert(tokens_valid(z)) by {
        assert forall|n:usize,i:int| #![trigger z.state.accumulators[n][i]] full::registered(z.state,n) && 0<=i<z.state.accumulators[n].len() implies {
            let token=z.state.accumulators[n][i];
            &&& token<z.history.len()
            &&& z.history[token as int].landed.receipt.actor==n
        } by {
            if n!=actor {assert(full::registered(a.state,n));}
            if n==actor && landing_rule(a,z,rule) && i==a.state.accumulators[n].len() {
                let recorded=entry(programs,a.state,actor);
                first_call_append(a.history,recorded,actor,a.state.iterators[actor].unwrap(),a.state);
                assert(z.state.accumulators[n][i]==call_token(a,actor));
            } else {
                assert(full::registered(a.state,n));
                assert(i<a.state.accumulators[n].len());
                assert(z.state.accumulators[n][i]==a.state.accumulators[n][i]);
                let token=a.state.accumulators[n][i];
                assert(token<a.history.len());
                assert(z.history[token as int]==a.history[token as int]);
            }
        }
    }
    assert(components_typed(programs,allowed,z.state)) by {
        assert forall|n:usize| full::registered(z.state,n) implies {
            &&& component_member(programs,allowed,z.state,n,z.state.effects[n])
            &&& (z.state.iterators[n].is_some() ==> component_member(programs,allowed,z.state,n,z.state.iterators[n].unwrap()))
        } by {
            if rule==control::Rule::Insert && n==actor { }
            else {
                assert(full::registered(a.state,n));
                assert(component_member(programs,allowed,a.state,n,a.state.effects[n]));
                if z.state.iterators[n].is_some() {
                    if n!=actor {assert(a.state.iterators[n]==z.state.iterators[n]);}
                    else if rule==control::Rule::Begin {assert(z.state.iterators[n]==Some(a.state.effects[n]));}
                    else if rule==control::Rule::Iter {
                        let result=entry(programs,a.state,actor).landed;
                        assert(result.next==z.state.iterators[n]);
                        assert(component_member(programs,allowed,a.state,n,result.next.unwrap()));
                    } else {
                        assert(a.state.iterators[n]==z.state.iterators[n]);
                    }
                }
            }
        }
    }
}

pub open spec fn execution<V,O>(programs:Programs<V,O>,allowed:grammar::Allowed<Port,V,O>,states:Seq<Configuration<V>>,labels:Seq<(usize,control::Rule)>) -> bool {
    states.len()==labels.len()+1 && forall|i:int| 0<=i<labels.len() ==> step(programs,allowed,states[i],states[i+1],labels[i].0,labels[i].1)
}

pub proof fn execution_preservation<V,O>(eq:spec_fn(Port,V,V)->bool,programs:Programs<V,O>,allowed:grammar::Allowed<Port,V,O>,
    states:Seq<Configuration<V>>,labels:Seq<(usize,control::Rule)>)
    requires grammar::primitive_theory(eq,allowed),execution(programs,allowed,states,labels),well_formed(programs,allowed,states.first()),
    ensures forall|i:int| 0<=i<states.len() ==> well_formed(programs,allowed,states[i]),
    decreases labels.len(),
{
    if labels.len()>0 {
        let previous=states.drop_last();let prefix=labels.drop_last();
        assert(execution(programs,allowed,previous,prefix)) by {
            assert forall|i:int| 0<=i<prefix.len() implies step(programs,allowed,previous[i],previous[i+1],prefix[i].0,prefix[i].1) by { }
        }
        execution_preservation(eq,programs,allowed,previous,prefix);
        configuration_preservation(eq,programs,allowed,previous.last(),states.last(),labels.last().0,labels.last().1);
        assert forall|i:int| 0<=i<states.len() implies well_formed(programs,allowed,states[i]) by {
            if i<previous.len() {assert(previous[i]==states[i]);} else {assert(i==states.len()-1);}
        }
    }
}

pub open spec fn empty<V>() -> Configuration<V> {Configuration {state:inv::empty(),history:Seq::empty()}}

pub proof fn empty_well_formed<V,O>(programs:Programs<V,O>,allowed:grammar::Allowed<Port,V,O>)
    ensures well_formed(programs,allowed,empty::<V>()),
{inv::empty_well_formed::<V>();}

/// Resource safety and authentic inverse records for every prefix reached from
/// the empty registry, with no intermediate well-formedness/footprint premise.
pub proof fn from_empty_safe<V,O>(eq:spec_fn(Port,V,V)->bool,programs:Programs<V,O>,allowed:grammar::Allowed<Port,V,O>,
    states:Seq<Configuration<V>>,labels:Seq<(usize,control::Rule)>)
    requires grammar::primitive_theory(eq,allowed),execution(programs,allowed,states,labels),states.first()==empty::<V>(),
    ensures forall|i:int| 0<=i<states.len() ==> inv::resource_safe(states[i].state)
        && tokens_valid(states[i]) && history_sound(programs,states[i].history),
{
    empty_well_formed(programs,allowed);
    execution_preservation(eq,programs,allowed,states,labels);
    assert forall|i:int| 0<=i<states.len() implies inv::resource_safe(states[i].state)
        && tokens_valid(states[i]) && history_sound(programs,states[i].history) by {
        assert(well_formed(programs,allowed,states[i]));
        assert forall|key:Port,left:usize,right:usize| full::publishes(states[i].state,key,left) && full::publishes(states[i].state,key,right) implies left==right by {
            assert(states[i].state.control.fibers[left].provisions.contains(key));
            assert(states[i].state.control.fibers[right].provisions.contains(key));
        }
    }
}

/// The successful interpreter is precisely the mediated table interpreter
/// after the paper's all-table projection. Provider resolution is justified by
/// the committed identity, rather than chosen from current Active providers.
pub proof fn run_projects<V,O>(node:grammar::Node<Port,V,O>,a:full::State<V>,actor:usize)
    requires inv::well_formed(a),run(node,a,actor).is_some(),
    ensures {
        let out=run(node,a,actor).unwrap();
        let projected=grammar::run(node,projection::project(a,ISet::full()));
        &&& projected.is_some()
        &&& projected.unwrap().state==projection::project(out.state,ISet::full())
        &&& projected.unwrap().next==out.next
    },
{
    match node {
        grammar::Node::Unit=>{},
        grammar::Node::Operation {key,operation,..}=>{
            resolution_sound(a,actor,key);
            let provider=resolve(a,actor,key).unwrap();
            projection::unique_owner(a);projection::lookup(a,ISet::full(),key,provider);
            let y=operation(a.tables[provider][key]).unwrap();
            projection::update_slot_projection(a,provider,key,Some(y.value));
        },
        grammar::Node::Provision {key,value,..}=>{
            projection::unique_owner(a);
            assert(!projection::project(a,ISet::full()).dom().contains(key)) by {
                if projection::project(a,ISet::full()).dom().contains(key) {
                    let provider=choose|p:usize| projection::owns(a,key,p);
                    assert(a.control.fibers[provider].provisions.contains(key));
                    assert(provider==actor);
                }
            }
            projection::update_slot_projection(a,actor,key,Some(value));
        },
    }
}

/// On an installed, well-typed component, committed resolution introduces no
/// additional failure relative to the mediated grammar. In particular a
/// provider's phase may already be Unloading: its committed table, rather than
/// Active-only publication, is still the operation's actual input.
pub proof fn run_definedness<V,O>(node:grammar::Node<Port,V,O>,allowed:grammar::Allowed<Port,V,O>,a:full::State<V>,actor:usize)
    requires inv::well_formed(a),full::registered(a,actor),a.control.fibers[actor].phase!=Phase::Inactive,
        grammar::permitted(allowed,a.control.fibers[actor].dependencies.union(a.control.fibers[actor].provisions),
            a.control.fibers[actor].provisions,node),
    ensures run(node,a,actor).is_some()==grammar::run(node,projection::project(a,ISet::full())).is_some(),
{
    if run(node,a,actor).is_some() {run_projects(node,a,actor);}
    if grammar::run(node,projection::project(a,ISet::full())).is_some() {
        projection::unique_owner(a);
        match node {
            grammar::Node::Unit=>{},
            grammar::Node::Operation {key,operation,..}=>{
                if !a.control.fibers[actor].provisions.contains(key) {
                    assert(a.control.fibers[actor].dependencies.contains(key));
                    let b=choose|b:Binding| a.control.fibers[actor].committed.contains(b) && b.key==key.key && b.realm==key.realm;
                    assert(names_key(b,key));
                    assert(resolve(a,actor,key).is_some());
                }
                resolution_sound(a,actor,key);
                let provider=resolve(a,actor,key).unwrap();
                let actual=choose|n:usize| projection::owns(a,key,n);
                assert(a.control.fibers[actual].provisions.contains(key));
                assert(provider==actual);
                projection::lookup(a,ISet::full(),key,provider);
            },
            grammar::Node::Provision {key,..}=>{
                assert(!a.tables[actor].dom().contains(key)) by {
                    if a.tables[actor].dom().contains(key) {
                        assert(projection::owns(a,key,actor));
                        projection::lookup(a,ISet::full(),key,actor);
                    }
                }
            },
        }
    }
}

pub open spec fn projected_inverse<V>(receipt:Receipt<V>) -> grammar::PartialMap<IMap<Port,V>> {
    match receipt.inverse {
        Inverse::Unit=>|s:IMap<Port,V>|Some(s),
        Inverse::Operation {key,undo,..}=>grammar::lift_inverse(key,undo),
        Inverse::Provision {key}=>|s:IMap<Port,V>| if s.dom().contains(key) {Some(s.remove(key))} else {None},
    }
}

pub proof fn inverse_projects<V>(receipt:Receipt<V>,a:full::State<V>)
    requires inv::well_formed(a),undo(receipt,a).is_some(),
    ensures projected_inverse(receipt)(projection::project(a,ISet::full()))
        ==Some(projection::project(undo(receipt,a).unwrap(),ISet::full())),
{
    projection::unique_owner(a);
    match receipt.inverse {
        Inverse::Unit=>{},
        Inverse::Operation {provider,key,undo:inverse}=>{
            resolution_sound(a,receipt.actor,key);
            projection::lookup(a,ISet::full(),key,provider);
            projection::update_slot_projection(a,provider,key,Some(inverse(a.tables[provider][key]).unwrap()));
        },
        Inverse::Provision {key}=>{
            projection::lookup(a,ISet::full(),key,receipt.actor);
            projection::update_slot_projection(a,receipt.actor,key,None);
        },
    }
}

pub proof fn missing_binding_fails<V,O>(node:grammar::Node<Port,V,O>,a:full::State<V>,actor:usize,key:Port,
    operation:grammar::Operation<V,O>,select:spec_fn(O)->Option<nat>)
    requires node==(grammar::Node::Operation {key,operation,select}),
        resolve(a,actor,key).is_none() || (resolve(a,actor,key).is_some()
            && (!full::registered(a,resolve(a,actor,key).unwrap()) || !a.tables[resolve(a,actor,key).unwrap()].dom().contains(key))),
    ensures run(node,a,actor).is_none(),
{ }

pub proof fn failed_inverse_blocks_unload<V,O>(programs:Programs<V,O>,allowed:grammar::Allowed<Port,V,O>,a:Configuration<V>,actor:usize)
    requires restore(a.history,a.state.accumulators[actor],a.state,actor).is_none(),
    ensures forall|z:Configuration<V>| !step(programs,allowed,a,z,actor,control::Rule::Unload),
{ }

/// Equality at one actual, successful application. The final-history catalog
/// below derives this equality for every landing in an execution.
pub open spec fn yielded_call_agrees<V,O>(model:full::Model<V>,programs:Programs<V,O>,a:Configuration<V>,actor:usize) -> bool {
    let out=run(programs(actor)(a.state.iterators[actor].unwrap()),a.state,actor);
    out.is_some() && (model.iterate)(actor,a.state.iterators[actor].unwrap(),a.state)
        ==full::Yield {state:out.unwrap().state,inverse:call_token(a,actor),next:out.unwrap().next}
}

pub open spec fn restore_calls_agree<V>(model:full::Model<V>,history:Seq<Entry<V>>,tokens:Seq<nat>,a:full::State<V>,actor:usize) -> bool
    decreases tokens.len(),
{
    if tokens.len()==0 {true}
    else {
        let token=tokens.last();
        &&& token<history.len() && history[token as int].landed.receipt.actor==actor
        &&& undo(history[token as int].landed.receipt,a).is_some()
        &&& (model.undo)(token,a)==undo(history[token as int].landed.receipt,a).unwrap()
        &&& restore_calls_agree(model,history,tokens.drop_last(),undo(history[token as int].landed.receipt,a).unwrap(),actor)
    }
}

pub proof fn restore_refines<V>(model:full::Model<V>,history:Seq<Entry<V>>,tokens:Seq<nat>,a:full::State<V>,actor:usize)
    requires inv::well_formed(a),restore_calls_agree(model,history,tokens,a,actor),
    ensures restore(history,tokens,a,actor)==Some(full::restore(model,tokens,a)),
        inv::admissible_restore(model,tokens,a,actor),
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let receipt=history[tokens.last() as int].landed.receipt;
        undo_preservation(receipt,a);
        restore_refines(model,history,tokens.drop_last(),undo(receipt,a).unwrap(),actor);
    }
}

pub open spec fn calls_agree<V,O>(model:full::Model<V>,programs:Programs<V,O>,a:Configuration<V>,z:Configuration<V>,actor:usize,rule:control::Rule) -> bool {
    (landing_rule(a,z,rule) ==> yielded_call_agrees(model,programs,a,actor))
        && (rule==control::Rule::Unload ==> restore_calls_agree(model,a.history,a.state.accumulators[actor],a.state,actor))
}

/// The original value-carrying relation follows from a successful partial step
/// and equality of the interpreter's actual calls. Local admissibility is a
/// conclusion of the constructed lift, not an additional refinement premise.
pub proof fn step_refines<V,O>(model:full::Model<V>,programs:Programs<V,O>,allowed:grammar::Allowed<Port,V,O>,a:Configuration<V>,z:Configuration<V>,actor:usize,rule:control::Rule)
    requires inv::well_formed(a.state),step(programs,allowed,a,z,actor,rule),calls_agree(model,programs,a,z,actor,rule),
    ensures full::step(model,a.state,z.state,actor,rule),inv::admissible_step(model,a.state,z.state,actor,rule),
{
    state_preservation(programs,allowed,a,z,actor,rule);
    metadata_frame(programs,allowed,a,z,actor,rule);
    if landing_rule(a,z,rule) {run_preservation(programs(actor)(a.state.iterators[actor].unwrap()),a.state,actor);}
    if rule==control::Rule::Unload {restore_refines(model,a.history,a.state.accumulators[actor],a.state,actor);}
    if rule==control::Rule::Insert {
        assert(full::auxiliary_frame(a.state,z.state,actor)) by {
            assert forall|n:usize| n!=actor && full::registered(a.state,n) implies z.state.tables[n]==a.state.tables[n]
                && z.state.effects[n]==a.state.effects[n] && z.state.iterators[n]==a.state.iterators[n]
                && z.state.accumulators[n]==a.state.accumulators[n] by { }
        }
    }
}

pub open spec fn erase_history<V>(states:Seq<Configuration<V>>) -> Seq<full::State<V>> {
    Seq::new(states.len(),|i:int|states[i].state)
}

pub proof fn execution_refines<V,O>(eq:spec_fn(Port,V,V)->bool,model:full::Model<V>,programs:Programs<V,O>,allowed:grammar::Allowed<Port,V,O>,
    states:Seq<Configuration<V>>,labels:Seq<(usize,control::Rule)>)
    requires grammar::primitive_theory(eq,allowed),execution(programs,allowed,states,labels),well_formed(programs,allowed,states.first()),
        forall|i:int| 0<=i<labels.len() ==> calls_agree(model,programs,states[i],states[i+1],labels[i].0,labels[i].1),
    ensures full::execution(model,erase_history(states),labels),inv::execution(model,erase_history(states),labels),
{
    execution_preservation(eq,programs,allowed,states,labels);
    assert forall|i:int| 0<=i<labels.len() implies full::step(model,erase_history(states)[i],erase_history(states)[i+1],labels[i].0,labels[i].1)
        && inv::admissible_step(model,erase_history(states)[i],erase_history(states)[i+1],labels[i].0,labels[i].1) by {
        step_refines(model,programs,allowed,states[i],states[i+1],labels[i].0,labels[i].1);
    }
}

pub open spec fn history_prefix<V>(a:Seq<Entry<V>>,z:Seq<Entry<V>>) -> bool {
    a.len()<=z.len() && forall|i:int| 0<=i<a.len() ==> #[trigger] a[i]==z[i]
}

pub proof fn history_prefix_transitive<V>(a:Seq<Entry<V>>,b:Seq<Entry<V>>,c:Seq<Entry<V>>)
    requires history_prefix(a,b),history_prefix(b,c),
    ensures history_prefix(a,c),
{
    assert forall|i:int| 0<=i<a.len() implies #[trigger] a[i]==c[i] by {assert(b[i]==c[i]);}
}

/// A found call keeps its first index in every extension of the history.
pub proof fn first_call_stable<V>(a:Seq<Entry<V>>,z:Seq<Entry<V>>,actor:usize,id:nat,input:full::State<V>)
    requires history_prefix(a,z),first_call(a,actor,id,input)<a.len(),
    ensures first_call(a,actor,id,input)==first_call(z,actor,id,input),
{
    first_call_properties(a,actor,id,input);
    first_call_properties(z,actor,id,input);
    let i=first_call(a,actor,id,input);
    let j=first_call(z,actor,id,input);
    assert(a[i as int]==z[i as int]);
    if j>i {assert(!same_call(z[i as int],actor,id,input));}
    if j<i {
        assert(a[j as int]==z[j as int]);
        assert(!same_call(a[j as int],actor,id,input));
    }
}

pub proof fn step_history_prefix<V,O>(programs:Programs<V,O>,allowed:grammar::Allowed<Port,V,O>,
    a:Configuration<V>,z:Configuration<V>,actor:usize,rule:control::Rule)
    requires step(programs,allowed,a,z,actor,rule),
    ensures history_prefix(a.history,z.history),
{
    assert(z.history==a.history || z.history==a.history.push(entry(programs,a.state,actor)));
    assert forall|i:int| 0<=i<a.history.len() implies #[trigger] a.history[i]==z.history[i] by { }
}

pub proof fn execution_history_prefix<V,O>(programs:Programs<V,O>,allowed:grammar::Allowed<Port,V,O>,
    states:Seq<Configuration<V>>,labels:Seq<(usize,control::Rule)>)
    requires execution(programs,allowed,states,labels),
    ensures forall|i:int| 0<=i<states.len() ==> history_prefix(states[i].history,states.last().history),
    decreases labels.len(),
{
    if labels.len()>0 {
        let previous=states.drop_last();let prefix=labels.drop_last();
        assert(execution(programs,allowed,previous,prefix)) by {
            assert forall|i:int| 0<=i<prefix.len() implies step(programs,allowed,previous[i],previous[i+1],prefix[i].0,prefix[i].1) by { }
        }
        execution_history_prefix(programs,allowed,previous,prefix);
        step_history_prefix(programs,allowed,previous.last(),states.last(),labels.last().0,labels.last().1);
        assert forall|i:int| 0<=i<states.len() implies history_prefix(states[i].history,states.last().history) by {
            if i<previous.len() {
                assert(previous[i]==states[i]);
                history_prefix_transitive(states[i].history,previous.last().history,states.last().history);
            } else {assert(i==states.len()-1);}
        }
    }
}

/// A single total mathematical Model for a finite actual execution. Its
/// observed calls come from authentic entries and actual partial inverses.
/// Values outside the recorded call/domain are an arbitrary mathematical
/// completion only: run, undo, restore and step retain their strict failures.
/// This completion is neither an executable fallback nor a progress theorem.
pub open spec fn catalog_model<V>(history:Seq<Entry<V>>) -> full::Model<V> {
    full::Model {
        iterate:|actor:usize,id:nat,input:full::State<V>| {
            let token=first_call(history,actor,id,input);
            if token<history.len() {
                let out=history[token as int].landed;
                full::Yield {state:out.state,inverse:token,next:out.next}
            } else {arbitrary::<full::Yield<V>>()}
        },
        undo:|token:nat,input:full::State<V>| {
            if token<history.len() && undo(history[token as int].landed.receipt,input).is_some() {
                undo(history[token as int].landed.receipt,input).unwrap()
            } else {arbitrary::<full::State<V>>()}
        },
    }
}

/// Determinism is supplied by the actual interpreter: entries with the same
/// actor, iterator and complete input have exactly the same captured receipt.
pub proof fn matching_entry_result<V,O>(programs:Programs<V,O>,history:Seq<Entry<V>>,i:int,
    actor:usize,id:nat,input:full::State<V>)
    requires history_sound(programs,history),0<=i<history.len(),same_call(history[i],actor,id,input),
    ensures run(programs(actor)(id),input,actor)==Some(history[i].landed),
{ }

pub proof fn catalog_landing_agrees<V,O>(programs:Programs<V,O>,allowed:grammar::Allowed<Port,V,O>,
    a:Configuration<V>,z:Configuration<V>,actor:usize,rule:control::Rule,history:Seq<Entry<V>>)
    requires inv::well_formed(a.state),step(programs,allowed,a,z,actor,rule),landing_rule(a,z,rule),
        history_prefix(z.history,history),history_sound(programs,history),
    ensures yielded_call_agrees(catalog_model(history),programs,a,actor),
{
    metadata_frame(programs,allowed,a,z,actor,rule);
    let recorded=entry(programs,a.state,actor);
    let id=a.state.iterators[actor].unwrap();
    first_call_append(a.history,recorded,actor,id,a.state);
    first_call_stable(z.history,history,actor,id,a.state);
    let token=call_token(a,actor);
    first_call_properties(history,actor,id,a.state);
    matching_entry_result(programs,history,token as int,actor,id,a.state);
}

pub proof fn catalog_restore_agrees<V>(history:Seq<Entry<V>>,catalog:Seq<Entry<V>>,tokens:Seq<nat>,a:full::State<V>,actor:usize)
    requires history_prefix(history,catalog),restore(history,tokens,a,actor).is_some(),
    ensures restore_calls_agree(catalog_model(catalog),history,tokens,a,actor),
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let token=tokens.last();
        assert(history[token as int]==catalog[token as int]);
        let next=undo(history[token as int].landed.receipt,a).unwrap();
        catalog_restore_agrees(history,catalog,tokens.drop_last(),next,actor);
    }
}

/// Every successful finite grammar execution refines one fixed value-carrying
/// Model. Call agreement and local admissibility are derived, not assumptions.
/// Failure freedom, arbitrary child primitives and host callbacks are outside
/// this theorem: a successful source execution remains an explicit premise.
pub proof fn catalog_execution_refines<V,O>(eq:spec_fn(Port,V,V)->bool,programs:Programs<V,O>,allowed:grammar::Allowed<Port,V,O>,
    states:Seq<Configuration<V>>,labels:Seq<(usize,control::Rule)>)
    requires grammar::primitive_theory(eq,allowed),execution(programs,allowed,states,labels),well_formed(programs,allowed,states.first()),
    ensures full::execution(catalog_model(states.last().history),erase_history(states),labels),
        inv::execution(catalog_model(states.last().history),erase_history(states),labels),
{
    execution_preservation(eq,programs,allowed,states,labels);
    execution_history_prefix(programs,allowed,states,labels);
    let model=catalog_model(states.last().history);
    assert forall|i:int| 0<=i<labels.len() implies calls_agree(model,programs,states[i],states[i+1],labels[i].0,labels[i].1) by {
        let a=states[i];let z=states[i+1];let actor=labels[i].0;let rule=labels[i].1;
        if landing_rule(a,z,rule) {catalog_landing_agrees(programs,allowed,a,z,actor,rule,states.last().history);}
        if rule==control::Rule::Unload {catalog_restore_agrees(a.history,states.last().history,a.state.accumulators[actor],a.state,actor);}
    }
    execution_refines(eq,model,programs,allowed,states,labels);
}

} // verus!
