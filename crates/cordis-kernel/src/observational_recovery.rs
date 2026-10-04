//! Entangled journal recovery modulo keywise observation.
//!
//! The action language and actual journals are shared with `entangled`. Only
//! local scalar respect/commutation and actual-input inverse witnesses are
//! required; no representative of an equivalence class is chosen. Identity
//! extension is a value interpretation and never licenses a failed source call.
#[cfg(verus_keep_ghost)]
use crate::{
    calculus as c, dependent_grammar as d, dependent_lift as dl, entangled as e,
    grammar_recovery as gr, mediated as m, observation as o, observational_grammar as weak,
    partial_domains as domains, partial_independence as partial, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn key_equivalence<V>(eq:spec_fn(Port,V,V)->bool)->bool {
    forall|key:Port| #[trigger] m::key_equivalence(eq,key)
}
pub open spec fn related<V>(eq:spec_fn(Port,V,V)->bool,a:IMap<Port,V>,b:IMap<Port,V>)->bool {
    o::context_equal(eq,ISet::full(),a,b)
}
pub proof fn context_equivalence<V>(eq:spec_fn(Port,V,V)->bool)
    requires key_equivalence(eq),
    ensures c::equivalence(|a:IMap<Port,V>,b:IMap<Port,V>|related(eq,a,b)),
{
    assert forall|key:Port| ISet::<Port>::full().contains(key) implies c::equivalence(|a:V,b:V|eq(key,a,b)) by {assert(m::key_equivalence(eq,key));}
    o::context_equivalence(eq,ISet::full());
    assert((|a:IMap<Port,V>,b:IMap<Port,V>|related(eq,a,b)) =~= (|a:IMap<Port,V>,b:IMap<Port,V>|o::context_equal(eq,ISet::full(),a,b)));
}
pub proof fn key_laws<V>(eq:spec_fn(Port,V,V)->bool,key:Port,a:V,b:V,z:V)
    requires key_equivalence(eq),
    ensures eq(key,a,a),eq(key,a,b) ==> eq(key,b,a),eq(key,a,b) && eq(key,b,z) ==> eq(key,a,z),
{
    assert(m::key_equivalence(eq,key));let rel=|x:V,y:V|eq(key,x,y);assert(c::equivalence(rel));
    assert(rel(a,a));if rel(a,b) {assert(rel(b,a));if rel(b,z) {assert(rel(a,z));}}
}
pub proof fn relation_laws<V>(eq:spec_fn(Port,V,V)->bool,a:IMap<Port,V>,b:IMap<Port,V>,z:IMap<Port,V>)
    requires key_equivalence(eq),
    ensures related(eq,a,a),related(eq,a,b) ==> related(eq,b,a),related(eq,a,b) && related(eq,b,z) ==> related(eq,a,z),
{
    context_equivalence(eq);
    let rel=|a:IMap<Port,V>,b:IMap<Port,V>|related(eq,a,b);
    assert(c::equivalence(rel));assert(rel(a,a));if rel(a,b) {assert(rel(b,a));if rel(b,z) {assert(rel(a,z));}}
}
pub open spec fn scalar_respects<V>(eq:spec_fn(Port,V,V)->bool,key:Port,f:spec_fn(V)->V)->bool {
    o::related_maps(|a:V,b:V|eq(key,a,b),f,f)
}
pub proof fn scalar_at<V>(eq:spec_fn(Port,V,V)->bool,key:Port,f:spec_fn(V)->V,a:V,b:V)
    requires scalar_respects(eq,key,f),eq(key,a,b),
    ensures eq(key,f(a),f(b)),
{let rel=|x:V,y:V|eq(key,x,y);assert(o::related_maps(rel,f,f));assert(rel(a,b));assert(rel(f(a),f(b)));}
pub open spec fn action_respects<V>(eq:spec_fn(Port,V,V)->bool,action:e::Action<V>)->bool {
    match action {e::Action::Operation {key,update}=>scalar_respects(eq,key,update),_=>true}
}
pub open spec fn word_respects<V>(eq:spec_fn(Port,V,V)->bool,word:Seq<e::Action<V>>)->bool {
    forall|i:int| 0<=i<word.len() ==> action_respects(eq,#[trigger] word[i])
}
pub proof fn apply_related<V>(eq:spec_fn(Port,V,V)->bool,action:e::Action<V>,a:IMap<Port,V>,b:IMap<Port,V>)
    requires key_equivalence(eq),action_respects(eq,action),related(eq,a,b),
    ensures related(eq,e::apply(action,a),e::apply(action,b)),
{
    let left=e::apply(action,a);let right=e::apply(action,b);
    assert forall|key:Port| ISet::<Port>::full().contains(key) implies
        left.dom().contains(key)==right.dom().contains(key) && (left.dom().contains(key) ==> eq(key,left[key],right[key])) by {
        if left.dom().contains(key) {key_laws(eq,key,left[key],left[key],left[key]);}assert(a.dom().contains(key)==b.dom().contains(key));
        match action {
            e::Action::Operation {key:k,update}=>{if k==key && a.dom().contains(key) {assert(eq(key,a[key],b[key]));scalar_at(eq,key,update,a[key],b[key]);}},
            _=>{},
        }
    }
}
pub proof fn restore_related<V>(eq:spec_fn(Port,V,V)->bool,journal:Seq<e::Action<V>>,a:IMap<Port,V>,b:IMap<Port,V>)
    requires key_equivalence(eq),word_respects(eq,journal),related(eq,a,b),
    ensures related(eq,e::restore(journal,a),e::restore(journal,b)),
    decreases journal.len(),
{
    if journal.len()>0 {
        apply_related(eq,journal.last(),a,b);
        restore_related(eq,journal.drop_last(),e::apply(journal.last(),a),e::apply(journal.last(),b));
    }
}
pub proof fn run_related<V>(eq:spec_fn(Port,V,V)->bool,word:Seq<e::Action<V>>,a:IMap<Port,V>,b:IMap<Port,V>)
    requires key_equivalence(eq),word_respects(eq,word),related(eq,a,b),
    ensures related(eq,e::run(word,a),e::run(word,b)),
    decreases word.len(),
{
    if word.len()>0 {
        run_related(eq,word.drop_last(),a,b);
        apply_related(eq,word.last(),e::run(word.drop_last(),a),e::run(word.drop_last(),b));
    }
}
/// Equal-key maps need only commute observationally at the same input.
/// Respect transports that equation through the rest of the real journal.
pub open spec fn atom_compatible<V>(eq:spec_fn(Port,V,V)->bool,inverse:e::Action<V>,foreign:e::Action<V>)->bool {
    match (inverse,foreign) {
        (e::Action::Operation {key:k,update:f},e::Action::Operation {key:j,update:g})=>
            k!=j || forall|v:V| #[trigger] eq(k,f(g(v)),g(f(v))),
        (_,e::Action::Provision {key,..})=>e::key(inverse)!=Some(key),
        _=>true,
    }
}
pub proof fn atomic_commutation<V>(eq:spec_fn(Port,V,V)->bool,inverse:e::Action<V>,foreign:e::Action<V>,state:IMap<Port,V>)
    requires key_equivalence(eq),e::inverse_action(inverse),atom_compatible(eq,inverse,foreign),
    ensures related(eq,e::apply(inverse,e::apply(foreign,state)),e::apply(foreign,e::apply(inverse,state))),
{
    let left=e::apply(inverse,e::apply(foreign,state));let right=e::apply(foreign,e::apply(inverse,state));
    assert forall|key:Port| ISet::<Port>::full().contains(key) implies
        left.dom().contains(key)==right.dom().contains(key) && (left.dom().contains(key) ==> eq(key,left[key],right[key])) by {
        if left.dom().contains(key) {key_laws(eq,key,left[key],left[key],left[key]);}
        if let e::Action::Operation {key:i,update:f}=inverse {
            if let e::Action::Operation {key:j,update:g}=foreign {
                if i==j && i==key && state.dom().contains(key) {assert(eq(key,f(g(state[key])),g(f(state[key]))));}
            }
        }
    }
}
pub proof fn atomwise_journal_commutation<V>(eq:spec_fn(Port,V,V)->bool,journal:Seq<e::Action<V>>,foreign:e::Action<V>,state:IMap<Port,V>)
    requires key_equivalence(eq),e::inverse_journal(journal),word_respects(eq,journal),
        forall|i:int| 0<=i<journal.len() ==> atom_compatible(eq,#[trigger] journal[i],foreign),
    ensures related(eq,e::restore(journal,e::apply(foreign,state)),e::apply(foreign,e::restore(journal,state))),
    decreases journal.len(),
{
    relation_laws(eq,e::apply(foreign,state),e::apply(foreign,state),e::apply(foreign,state));
    if journal.len()>0 {
        let prefix=journal.drop_last();let inverse=journal.last();
        atomic_commutation(eq,inverse,foreign,state);
        restore_related(eq,prefix,e::apply(inverse,e::apply(foreign,state)),e::apply(foreign,e::apply(inverse,state)));
        atomwise_journal_commutation(eq,prefix,foreign,e::apply(inverse,state));
        relation_laws(eq,e::restore(journal,e::apply(foreign,state)),e::restore(prefix,e::apply(foreign,e::apply(inverse,state))),e::apply(foreign,e::restore(journal,state)));
    }
}
pub open spec fn compatible<V>(eq:spec_fn(Port,V,V)->bool,journal:Seq<e::Action<V>>,foreign:e::Action<V>)->bool {
    match foreign {
        e::Action::Operation {key,..} if e::erases(journal,key)=>true,
        _=>forall|i:int| 0<=i<journal.len() ==> atom_compatible(eq,#[trigger] journal[i],foreign),
    }
}
pub proof fn journal_commutation<V>(eq:spec_fn(Port,V,V)->bool,journal:Seq<e::Action<V>>,foreign:e::Action<V>,state:IMap<Port,V>)
    requires key_equivalence(eq),e::inverse_journal(journal),word_respects(eq,journal),compatible(eq,journal,foreign),
    ensures related(eq,e::restore(journal,e::apply(foreign,state)),e::apply(foreign,e::restore(journal,state))),
{
    context_equivalence(eq);
    match foreign {
        e::Action::Operation {key,update} if e::erases(journal,key)=>{e::entangled_absorption(journal,state,key,update);relation_laws(eq,e::restore(journal,state),e::restore(journal,state),e::restore(journal,state));},
        _=>{atomwise_journal_commutation(eq,journal,foreign,state);},
    }
}
pub open spec fn word_compatible<V>(eq:spec_fn(Port,V,V)->bool,journal:Seq<e::Action<V>>,foreign:Seq<e::Action<V>>)->bool {
    forall|i:int| 0<=i<foreign.len() ==> compatible(eq,journal,#[trigger] foreign[i])
}
pub proof fn journal_word_commutation<V>(eq:spec_fn(Port,V,V)->bool,journal:Seq<e::Action<V>>,foreign:Seq<e::Action<V>>,state:IMap<Port,V>)
    requires key_equivalence(eq),e::inverse_journal(journal),word_respects(eq,journal),word_respects(eq,foreign),word_compatible(eq,journal,foreign),
    ensures related(eq,e::restore(journal,e::run(foreign,state)),e::run(foreign,e::restore(journal,state))),
    decreases foreign.len(),
{
    relation_laws(eq,e::restore(journal,state),e::restore(journal,state),e::restore(journal,state));
    if foreign.len()>0 {
        let prefix=foreign.drop_last();let last=foreign.last();
        journal_word_commutation(eq,journal,prefix,state);
        journal_commutation(eq,journal,last,e::run(prefix,state));
        apply_related(eq,last,e::restore(journal,e::run(prefix,state)),e::run(prefix,e::restore(journal,state)));
        relation_laws(eq,e::restore(journal,e::run(foreign,state)),e::apply(last,e::restore(journal,e::run(prefix,state))),e::run(foreign,e::restore(journal,state)));
    }
}
/// Only local conditions at actual forward inputs, not a requested end-state
/// recovery equality. Foreign compatibility is against the already returned
/// journal; own inverses need no uniform inverse law over all source inputs.
pub open spec fn admissible_trace<V>(eq:spec_fn(Port,V,V)->bool,events:Seq<e::Event<V>>,initial:IMap<Port,V>)->bool
    decreases events.len(),
{
    events.len()==0 || {
        let prefix=events.drop_last();let before=e::trace_state(prefix,initial);let last=events.last();
        &&& admissible_trace(eq,prefix,initial)
        &&& match last.returned {
            Some(inverse)=>e::inverse_action(inverse) && action_respects(eq,inverse)
                && related(eq,e::apply(inverse,e::run(last.forward,before)),before),
            None=>word_respects(eq,last.forward) && word_compatible(eq,e::journal(prefix),last.forward),
        }
    }
}
pub proof fn entangled_recovery<V>(eq:spec_fn(Port,V,V)->bool,events:Seq<e::Event<V>>,initial:IMap<Port,V>)
    requires key_equivalence(eq),admissible_trace(eq,events,initial),
    ensures e::inverse_journal(e::journal(events)),word_respects(eq,e::journal(events)),
        related(eq,e::restore(e::journal(events),e::trace_state(events,initial)),e::foreign_state(events,initial)),
    decreases events.len(),
{
    relation_laws(eq,initial,initial,initial);
    if events.len()>0 {
        let prefix=events.drop_last();let before=e::trace_state(prefix,initial);let last=events.last();
        entangled_recovery(eq,prefix,initial);
        match last.returned {
            Some(inverse)=>{
                assert(e::journal(events).drop_last()==e::journal(prefix));assert(e::journal(events).last()==inverse);
                assert forall|i:int| 0<=i<e::journal(events).len() implies e::inverse_action(#[trigger] e::journal(events)[i])
                    && action_respects(eq,e::journal(events)[i]) by {if i<e::journal(prefix).len() {assert(e::journal(events)[i]==e::journal(prefix)[i]);}}
                restore_related(eq,e::journal(prefix),e::apply(inverse,e::run(last.forward,before)),before);
                relation_laws(eq,e::restore(e::journal(events),e::trace_state(events,initial)),e::restore(e::journal(prefix),before),e::foreign_state(events,initial));
            },
            None=>{
                journal_word_commutation(eq,e::journal(prefix),last.forward,before);
                run_related(eq,last.forward,e::restore(e::journal(prefix),before),e::foreign_state(prefix,initial));
                relation_laws(eq,e::restore(e::journal(events),e::trace_state(events,initial)),e::run(last.forward,e::restore(e::journal(prefix),before)),e::foreign_state(events,initial));
            },
        }
    }
}
/// Strict partial respect is sufficient for the identity extension to respect
/// observation. This does not assert that a failed call becomes a source step.
pub proof fn total_respects<V>(eq:spec_fn(Port,V,V)->bool,key:Port,f:m::PartialMap<V>)
    requires m::partial_related(|a:V,b:V|eq(key,a,b),f,f),
    ensures scalar_respects(eq,key,gr::total(f)),
{
    assert forall|a:V,b:V| eq(key,a,b) implies #[trigger] eq(key,gr::total(f)(a),gr::total(f)(b)) by {
        assert(f(a).is_some()==f(b).is_some());
    }
}

/// The interface is observational: hidden representation differences in either
/// order are allowed. It is strictly weaker than exact scalar commutation.
pub open spec fn independent_keys<A,X,U,B>(eq:spec_fn(Port,U,U)->bool,lib:dl::Library<A,X,U,B>)->bool {
    forall|key:Port,f:spec_fn(U)->U,g:spec_fn(U)->U| gr::generator(lib,key,f) && gr::generator(lib,key,g)
        ==> forall|v:U| #[trigger] eq(key,f(g(v)),g(f(v)))
}
pub proof fn forward_respects<U,B>(eq:spec_fn(Port,U,U)->bool,key:Port,op:m::Operation<U,B>)
    requires weak::operation_respects(|a:U,b:U|eq(key,a,b),op),
    ensures scalar_respects(eq,key,gr::forward(op)),
{
    assert forall|a:U,b:U| eq(key,a,b) implies #[trigger] eq(key,gr::forward(op)(a),gr::forward(op)(b)) by {
        assert(op(a).is_some()==op(b).is_some());
    }
}
/// Every actual inverse generator inherits observation respect from the yield
/// relation at its original successful input; no new inverse is synthesized.
pub proof fn generator_respects<A,X,U,B>(eq:spec_fn(Port,U,U)->bool,lib:dl::Library<A,X,U,B>,key:Port,f:spec_fn(U)->U)
    requires weak::primitive_theory(eq,lib),gr::generator(lib,key,f),
    ensures scalar_respects(eq,key,f),
{
    let (a,x)=choose|a:A,x:X|lib.allowed.contains(a) && #[trigger] (lib.arguments)(a,x) && (lib.key)(a)==key && {
        let op=(lib.apply)(a,x);
        f==gr::forward(op) || exists|v:U| #[trigger] op(v).is_some() && f==gr::total(op(v).unwrap().undo)
    };
    let op=(lib.apply)(a,x);assert(d::operation_typed(lib,a,x));assert(weak::operation_admissible(|u:U,v:U|eq(key,u,v),op));
    if f==gr::forward(op) {forward_respects(eq,key,op);}
    else {
        let before=choose|v:U| #[trigger] op(v).is_some() && f==gr::total(op(v).unwrap().undo);
        assert(m::key_equivalence(eq,key));assert(eq(key,before,before));
        assert(m::partial_related(|u:U,v:U|eq(key,u,v),op(before).unwrap().undo,op(before).unwrap().undo));
        total_respects(eq,key,op(before).unwrap().undo);
    }
}
pub proof fn typed_action_respects<A,X,U,B>(eq:spec_fn(Port,U,U)->bool,lib:dl::Library<A,X,U,B>,action:e::Action<U>)
    requires weak::primitive_theory(eq,lib),gr::action_typed(lib,action),
    ensures action_respects(eq,action),
{
    if let e::Action::Operation {key,update}=action {generator_respects(eq,lib,key,update);}
}
pub proof fn interface_compatible<A,X,U,B>(eq:spec_fn(Port,U,U)->bool,lib:dl::Library<A,X,U,B>,journal:Seq<e::Action<U>>,foreign:e::Action<U>,keys:ISet<Port>)
    requires independent_keys(eq,lib),e::inverse_journal(journal),gr::scope(journal,keys),
        forall|i:int| 0<=i<journal.len() ==> gr::action_typed(lib,#[trigger] journal[i]),gr::action_typed(lib,foreign),
        match foreign {e::Action::Provision {key,..}=>!keys.contains(key),_=>true},
    ensures compatible(eq,journal,foreign),
{
    assert forall|i:int| 0<=i<journal.len() implies atom_compatible(eq,#[trigger] journal[i],foreign) by {
        match (journal[i],foreign) {
            (e::Action::Operation {key:k,update:f},e::Action::Operation {key:j,update:g})=>{
                if k==j {assert(gr::generator(lib,k,f));assert(gr::generator(lib,k,g));}
            },
            (_,e::Action::Provision {key,..})=>{if e::key(journal[i]).is_some() {assert(keys.contains(e::key(journal[i]).unwrap()));}},
            _=>{},
        }
    }
}

/// Strict partial commutation plus each successful forward's observational
/// inverse witness proves the corresponding identity-extension commutation.
/// This uses actual domain transport; arbitrary returned inverses are not
/// silently assumed to possess inverse witnesses of their own.
pub proof fn partial_forward_commutation<V>(eq:spec_fn(Port,V,V)->bool,key:Port,
    f:m::PartialMap<V>,g:m::PartialMap<V>,inverses:spec_fn(V)->m::PartialMap<V>)
    requires key_equivalence(eq),partial::respects(|a:V,b:V|eq(key,a,b),g),
        partial::commutes(|a:V,b:V|eq(key,a,b),f,g),
        forall|v:V| #[trigger] f(v).is_some() ==> {
            let undo=inverses(v);
            &&& undo(f(v).unwrap()).is_some()
            &&& eq(key,undo(f(v).unwrap()).unwrap(),v)
            &&& partial::commutes(|a:V,b:V|eq(key,a,b),undo,g)
        },
    ensures forall|v:V| #[trigger] eq(key,gr::total(f)(gr::total(g)(v)),gr::total(g)(gr::total(f)(v))),
{
    let local=|a:V,b:V|eq(key,a,b);
    assert forall|v:V| #[trigger] eq(key,gr::total(f)(gr::total(g)(v)),gr::total(g)(gr::total(f)(v))) by {
        assert(partial::optional_equal(local,partial::compose(f,g)(v),partial::compose(g,f)(v)));
        if f(v).is_some() && g(v).is_some() {domains::enabled_diamond(local,f,g,inverses(v),v);}
        else if f(v).is_some() {assert(g(f(v).unwrap()).is_none());key_laws(eq,key,f(v).unwrap(),f(v).unwrap(),f(v).unwrap());}
        else if g(v).is_some() {assert(f(g(v).unwrap()).is_none());key_laws(eq,key,g(v).unwrap(),g(v).unwrap(),g(v).unwrap());}
        else {key_laws(eq,key,v,v,v);}
    }
}

}
