//! Actual continuation after an observational iteration diamond.
//!
//! Historical entries remain authentic applications on each side. A fixed
//! transposition renames the two swapped tokens, and newly appended tokens are
//! fresh fixed points. Captured provider/key/owner names are preserved while
//! inverse functions need only agree on their strict observational domains.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, dependent_lift as dep, global, grammar_lift as lift, mediated as m,
    mixed_grammar as g, mixed_iteration_exchange as ix, mixed_observational_runs as obs,
    mixed_transposition as mx, observational_grammar as og, observational_lift as ol,
    refinement as r, semantics as s, Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn token(h:nat,t:nat)->nat { if t==h {h+1} else if t==h+1 {h} else {t} }
pub open spec fn tokens(h:nat,source:Seq<nat>)->Seq<nat> {
    Seq::new(source.len(),|i:int|token(h,source[i]))
}
pub proof fn token_laws(h:nat,t:nat,len:nat)
    requires h+2<=len,
    ensures token(h,token(h,t))==t,(t<len)==(token(h,t)<len),token(h,len)==len,
{ }
pub proof fn tokens_laws(h:nat,source:Seq<nat>,fresh:nat)
    ensures tokens(h,source.push(fresh))==tokens(h,source).push(token(h,fresh)),
        source.len()>0 ==> tokens(h,source).last()==token(h,source.last())
            && tokens(h,source.drop_last())==tokens(h,source).drop_last(),
        tokens(h,Seq::empty())==Seq::<nat>::empty(),
{
    assert(tokens(h,source.push(fresh)) =~= tokens(h,source).push(token(h,fresh)));
    if source.len()>0 {assert(tokens(h,source.drop_last()) =~= tokens(h,source).drop_last());}
}
pub open spec fn state_related<U>(eq:spec_fn(Port,U,U)->bool,h:nat,a:s::State<U>,b:s::State<U>)->bool {
    &&& obs::tables_related(eq,a,b) && a.effects==b.effects && a.iterators==b.iterators
    &&& a.accumulators.dom()==b.accumulators.dom()
    &&& forall|id:usize| a.accumulators.dom().contains(id) ==> b.accumulators[id]==tokens(h,a.accumulators[id])
}
pub open spec fn histories_related<U,I>(eq:spec_fn(Port,U,U)->bool,h:nat,a:Seq<g::Entry<U,I>>,b:Seq<g::Entry<U,I>>)->bool {
    &&& h+2<=a.len() && a.len()==b.len()
    &&& forall|i:nat| #![trigger a[i as int]] i<a.len() ==> {
        let x=a[i as int];let y=b[token(h,i) as int];
        &&& x.iterator==y.iterator && x.landed.next==y.landed.next && x.landed.spawn==y.landed.spawn
        &&& obs::receipt_related(eq,x.landed.receipt,y.landed.receipt)
    }
}
pub open spec fn related<U,I>(eq:spec_fn(Port,U,U)->bool,h:nat,a:g::Configuration<U,I>,b:g::Configuration<U,I>)->bool {
    state_related(eq,h,a.state,b.state) && a.roots==b.roots && a.current==b.current
        && histories_related(eq,h,a.history,b.history)
}

/// A successful source inverse supplies its real domain. No success of the
/// other inverse, including a captured child retirement, is assumed.
pub proof fn undo_observations<U>(eq:spec_fn(Port,U,U)->bool,left:g::Receipt<U>,right:g::Receipt<U>,a:s::State<U>,b:s::State<U>)
    requires obs::tables_related(eq,a,b),obs::receipt_related(eq,left,right),g::undo(left,a).is_some(),
    ensures g::undo(right,b).is_some(),obs::tables_related(eq,g::undo(left,a).unwrap(),g::undo(right,b).unwrap()),
{
    match (left,right) {
        (g::Receipt::Table {receipt:x},g::Receipt::Table {receipt:y})=>{
            match (x.inverse,y.inverse) {
                (lift::Inverse::Operation {provider,key,undo:f},lift::Inverse::Operation {undo:g,..})=>{
                    let u=a.tables[provider][key];let v=b.tables[provider][key];
                    assert(eq(key,u,v));assert(m::partial_related(|u:U,v:U|eq(key,u,v),f,g));
                    assert(g(v).is_some());assert(eq(key,f(u).unwrap(),g(v).unwrap()));
                    obs::update_related(eq,a,b,provider,key,Some(f(u).unwrap()),Some(g(v).unwrap()));
                },
                (lift::Inverse::Provision {key},lift::Inverse::Provision {..})=>{obs::update_related(eq,a,b,x.actor,key,None,None);},
                _=>{},
            }
        },
        (g::Receipt::Child {child,..},g::Receipt::Child {..})=>{
            let x=g::undo(left,a).unwrap();let y=g::undo(right,b).unwrap();
            assert(x.control.fibers.dom() =~= a.control.fibers.dom());
            assert forall|id:usize| s::registered(x,id) implies x.tables[id].dom()==y.tables[id].dom()
                && forall|key:Port| x.tables[id].dom().contains(key) ==> eq(key,x.tables[id][key],y.tables[id][key]) by {
                assert(s::registered(a,id));
            }
        },_=>{},
    }

}

pub proof fn undo_transport<U>(eq:spec_fn(Port,U,U)->bool,h:nat,left:g::Receipt<U>,right:g::Receipt<U>,a:s::State<U>,b:s::State<U>)
    requires state_related(eq,h,a,b),obs::receipt_related(eq,left,right),g::undo(left,a).is_some(),
    ensures g::undo(right,b).is_some(),state_related(eq,h,g::undo(left,a).unwrap(),g::undo(right,b).unwrap()),
{
    undo_observations(eq,left,right,a,b);
}

pub proof fn restore_transport<U,I>(eq:spec_fn(Port,U,U)->bool,h:nat,left:Seq<g::Entry<U,I>>,right:Seq<g::Entry<U,I>>,
    stack:Seq<nat>,a:s::State<U>,b:s::State<U>,actor:usize)
    requires histories_related(eq,h,left,right),state_related(eq,h,a,b),g::restore(left,stack,a,actor).is_some(),
    ensures g::restore(right,tokens(h,stack),b,actor).is_some(),
        state_related(eq,h,g::restore(left,stack,a,actor).unwrap(),g::restore(right,tokens(h,stack),b,actor).unwrap()),
    decreases stack.len(),
{
    tokens_laws(h,stack,0);
    if stack.len()>0 {
        let t=stack.last();token_laws(h,t,left.len());
        let x=left[t as int].landed.receipt;let y=right[token(h,t) as int].landed.receipt;
        assert(obs::receipt_related(eq,x,y));assert(g::owner(x)==g::owner(y));
        undo_transport(eq,h,x,y,a,b);
        restore_transport(eq,h,left,right,stack.drop_last(),g::undo(x,a).unwrap(),g::undo(y,b).unwrap(),actor);
    }
}

pub proof fn targets<U>(eq:spec_fn(Port,U,U)->bool,a:s::State<U>,b:s::State<U>,actor:usize,view:ISet<Binding>)
    requires obs::tables_related(eq,a,b),
    ensures s::target(a,actor,view)==s::target(b,actor,view),s::coherent(a,actor)==s::coherent(b,actor),
{
    assert forall|key:Port,id:usize| s::publishes(a,key,id)==s::publishes(b,key,id) by {}
}

pub proof fn unreferenced<U,I>(eq:spec_fn(Port,U,U)->bool,h:nat,a:g::Configuration<U,I>,b:g::Configuration<U,I>,child:usize)
    requires related(eq,h,a,b),s::shaped(a.state),g::tokens_valid(a),ch::remove_unreferenced(g::kind(a.history),a.state,child),
    ensures ch::remove_unreferenced(g::kind(b.history),b.state,child),
{
    assert forall|owner:usize,t:nat| s::registered(b.state,owner) && b.state.accumulators[owner].contains(t)
        implies g::kind(b.history)(t)!=Some(child) by {
        let i=choose|i:int| 0<=i<b.state.accumulators[owner].len() && b.state.accumulators[owner][i]==t;
        assert(a.state.accumulators.dom().contains(owner));
        assert(b.state.accumulators[owner]==tokens(h,a.state.accumulators[owner]));
        let old=a.state.accumulators[owner][i];
        assert(t==token(h,old));assert(a.state.accumulators[owner].contains(old));assert(old<a.history.len());
        assert(obs::receipt_related(eq,a.history[old as int].landed.receipt,b.history[t as int].landed.receipt));
        assert(g::captured_child(a.history[old as int].landed.receipt)==g::captured_child(b.history[t as int].landed.receipt));
    }
}

pub open spec fn successor<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    left:g::Configuration<U,I>,next:g::Configuration<U,I>,right:g::Configuration<U,I>,actor:usize,rule:r::Rule)->g::Configuration<U,I> {
    match rule {
        r::Rule::Insert=>{let f=next.state.control.fibers[actor];mx::insert(right,actor,f.parent,f.dependencies,f.provisions,next.roots[actor])},
        r::Rule::Retire=>g::Configuration {state:s::with_control(right.state,global::retire_fiber(right.state.control,actor)),..right},
        r::Rule::Remove=>g::Configuration {state:s::erase(right.state,actor),roots:right.roots.remove(actor),current:right.current.remove(actor),history:right.history},
        r::Rule::Begin=>g::edit(right,actor,Phase::Loading,next.state.control.fibers[actor].committed,Some(right.roots[actor]),Seq::empty()),
        r::Rule::Iter | r::Rule::Finish=>g::land(lib,programs,right,actor,mx::landing_phase(rule)),
        r::Rule::Divert=>if g::landing(left,next,rule) {g::land(lib,programs,right,actor,Phase::Unloading)}
            else {g::edit(right,actor,Phase::Unloading,right.state.control.fibers[actor].committed,None,right.state.accumulators[actor])},
        r::Rule::Leave=>g::edit(right,actor,Phase::Unloading,right.state.control.fibers[actor].committed,None,right.state.accumulators[actor]),
        r::Rule::Unload=>g::unload(right,actor),
        _=>right,
    }
}

pub proof fn edit_related<U>(eq:spec_fn(Port,U,U)->bool,h:nat,a:s::State<U>,b:s::State<U>,actor:usize,
    phase:Phase,committed:ISet<Binding>,iterator:Option<nat>,stack:Seq<nat>)
    requires state_related(eq,h,a,b),s::registered(a,actor),
    ensures state_related(eq,h,s::edit(a,actor,phase,committed,iterator,stack),s::edit(b,actor,phase,committed,iterator,tokens(h,stack))),
{
    let x=s::edit(a,actor,phase,committed,iterator,stack);let y=s::edit(b,actor,phase,committed,iterator,tokens(h,stack));
    assert forall|id:usize| x.accumulators.dom().contains(id) implies y.accumulators[id]==tokens(h,x.accumulators[id]) by {}
    assert forall|id:usize| s::registered(x,id) implies x.tables[id].dom()==y.tables[id].dom()
        && forall|key:Port| x.tables[id].dom().contains(key) ==> eq(key,x.tables[id][key],y.tables[id][key]) by {assert(s::registered(a,id));}
}
pub proof fn append_history<U,I>(eq:spec_fn(Port,U,U)->bool,h:nat,a:Seq<g::Entry<U,I>>,b:Seq<g::Entry<U,I>>,x:g::Entry<U,I>,y:g::Entry<U,I>)
    requires histories_related(eq,h,a,b),x.iterator==y.iterator,x.landed.next==y.landed.next,x.landed.spawn==y.landed.spawn,
        obs::receipt_related(eq,x.landed.receipt,y.landed.receipt),
    ensures histories_related(eq,h,a.push(x),b.push(y)),
{
    assert forall|i:nat| #![trigger a.push(x)[i as int]] i<a.push(x).len() implies {
        let u=a.push(x)[i as int];let v=b.push(y)[token(h,i) as int];
        &&& u.iterator==v.iterator && u.landed.next==v.landed.next && u.landed.spawn==v.landed.spawn
        &&& obs::receipt_related(eq,u.landed.receipt,v.landed.receipt)
    } by {
        token_laws(h,i,a.len());
        if i<a.len() {assert(a.push(x)[i as int]==a[i as int]);assert(b.push(y)[token(h,i) as int]==b[token(h,i) as int]);}
        else {assert(i==a.len());assert(token(h,i)==i);}
    }
}
pub proof fn run_aux<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,h:nat,lib:g::Library<A,X,U,B>,node:g::Node<A,X,U,B,I>,a:s::State<U>,b:s::State<U>,actor:usize)
    requires state_related(eq,h,a,b),g::run(lib,node,a,actor).is_some(),g::run(lib,node,b,actor).is_some(),
        obs::tables_related(eq,g::run(lib,node,a,actor).unwrap().state,g::run(lib,node,b,actor).unwrap().state),
    ensures state_related(eq,h,g::run(lib,node,a,actor).unwrap().state,g::run(lib,node,b,actor).unwrap().state),
{
    let x=g::run(lib,node,a,actor).unwrap().state;let y=g::run(lib,node,b,actor).unwrap().state;
    tokens_laws(h,Seq::empty(),0);
    assert forall|id:usize| x.accumulators.dom().contains(id) implies y.accumulators[id]==tokens(h,x.accumulators[id]) by {
        match node {g::Node::Child {child,..}=>{if id==child {assert(x.accumulators[id].len()==0);}},_=>{},}
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn step_transport<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,h:nat,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    left:g::Configuration<U,I>,next:g::Configuration<U,I>,right:g::Configuration<U,I>,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,left),g::well_formed(lib,programs,right),
        related(eq,h,left,right),g::step(lib,programs,left,next,actor,rule),
    ensures {
        let result=successor(lib,programs,left,next,right,actor,rule);
        &&& g::step(lib,programs,right,result,actor,rule) && related(eq,h,next,result)
        &&& g::well_formed(lib,programs,next) && g::well_formed(lib,programs,result)
        &&& g::landing(left,next,rule)==g::landing(right,result,rule)
        &&& (g::landing(left,next,rule) ==> result.history==right.history.push(g::entry(lib,programs,right,actor))
            && result.history.last().input==right.state)
    },
{
    let result=successor(lib,programs,left,next,right,actor,rule);
    targets(eq,left.state,right.state,actor,next.state.control.fibers[actor].committed);
    tokens_laws(h,Seq::empty(),0);
    if g::landing(left,next,rule) {
        let id=left.current[actor].unwrap();let node=programs(actor)(id);
        ol::run_members(eq,lib,programs,left.state,actor,id);
        obs::run_transport(eq,lib,node,left.state,right.state,actor);
        let x=g::entry(lib,programs,left,actor);let y=g::entry(lib,programs,right,actor);
        append_history(eq,h,left.history,right.history,x,y);
        run_aux(eq,h,lib,node,left.state,right.state,actor);
        token_laws(h,left.history.len(),left.history.len());tokens_laws(h,left.state.accumulators[actor],left.history.len());
        assert(tokens(h,left.state.accumulators[actor].push(left.history.len()))==right.state.accumulators[actor].push(right.history.len()));
        let phase=mx::landing_phase(rule);let cont=if phase==Phase::Loading {x.landed.next} else {None};
        edit_related(eq,h,x.landed.state,y.landed.state,actor,phase,left.state.control.fibers[actor].committed,dep::marker(cont),left.state.accumulators[actor].push(left.history.len()));
        assert(next==g::land(lib,programs,left,actor,phase));
        assert(related(eq,h,next,result));
    } else {
        match rule {
            r::Rule::Insert | r::Rule::Retire=>{
                assert(next.state.control.fibers =~= result.state.control.fibers) by {
                    assert forall|id:usize| next.state.control.fibers.dom().contains(id)==result.state.control.fibers.dom().contains(id) by {if id!=actor {assert(r::registered(left.state.control,id)==r::registered(next.state.control,id));}}
                    assert forall|id:usize| next.state.control.fibers.dom().contains(id) implies next.state.control.fibers[id]==result.state.control.fibers[id] by {if id!=actor {assert(r::registered(left.state.control,id));assert(next.state.control.fibers[id]==left.state.control.fibers[id]);}}
                }
            },
            r::Rule::Remove=>{unreferenced(eq,h,left,right,actor);},
            r::Rule::Unload=>{
                restore_transport(eq,h,left.history,right.history,left.state.accumulators[actor],left.state,right.state,actor);
                let a=g::restore(left.history,left.state.accumulators[actor],left.state,actor).unwrap();
                let b=g::restore(right.history,right.state.accumulators[actor],right.state,actor).unwrap();
                g::restore_preservation(lib,programs,left.history,left.state.accumulators[actor],left.state,actor);
                edit_related(eq,h,a,b,actor,Phase::Inactive,ISet::empty(),None,Seq::empty());
            },
            r::Rule::Begin=>{edit_related(eq,h,left.state,right.state,actor,Phase::Loading,next.state.control.fibers[actor].committed,dep::marker(Some(left.roots[actor])),Seq::empty());},
            r::Rule::Leave | r::Rule::Divert=>{edit_related(eq,h,left.state,right.state,actor,Phase::Unloading,left.state.control.fibers[actor].committed,None,left.state.accumulators[actor]);},
            _=>{},
        }
        assert forall|id:usize| next.state.accumulators.dom().contains(id) implies result.state.accumulators[id]==tokens(h,next.state.accumulators[id]) by {
            match rule {r::Rule::Insert=>{if id==actor {assert(next.state.accumulators[id].len()==0);}},_=>{},}
        }
        assert forall|id:usize| s::registered(next.state,id) implies next.state.tables[id].dom()==result.state.tables[id].dom()
            && forall|key:Port| next.state.tables[id].dom().contains(key) ==> eq(key,next.state.tables[id][key],result.state.tables[id][key]) by {
            match rule {
                r::Rule::Insert=>{if id==actor {assert(next.state.tables[id].is_empty());} else {assert(s::registered(left.state,id));}},
                r::Rule::Retire | r::Rule::Remove=>{assert(s::registered(left.state,id));},
                _=>{},
            }
        }
        assert(related(eq,h,next,result));
    }
    assert(g::step(lib,programs,right,result,actor,rule));
    ol::configuration_preservation(eq,lib,programs,left,next,actor,rule);
    ol::configuration_preservation(eq,lib,programs,right,result,actor,rule);
}

/// Construct each successor using the target's own interpreter and history.
pub open spec fn transport<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,start:g::Configuration<U,I>)->Seq<g::Configuration<U,I>>
    decreases labels.len(),
{
    if labels.len()==0 {seq![start]}
    else {
        let prefix=transport(lib,programs,source.drop_last(),labels.drop_last(),start);
        prefix.push(successor(lib,programs,source[source.len()-2],source.last(),prefix.last(),labels.last().0,labels.last().1))
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn suffix_transport<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,h:nat,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,start:g::Configuration<U,I>)
    requires og::primitive_theory(eq,lib),g::execution(lib,programs,source,labels),related(eq,h,source.first(),start),
        g::well_formed(lib,programs,source.first()),g::well_formed(lib,programs,start),
    ensures {
        let result=transport(lib,programs,source,labels,start);
        &&& result.len()==source.len() && result.first()==start && g::execution(lib,programs,result,labels)
        &&& forall|i:int| 0<=i<source.len() ==> related(eq,h,source[i],result[i]) && g::well_formed(lib,programs,result[i])
    },
    decreases labels.len(),
{
    hide(related);hide(g::well_formed);hide(g::step);hide(successor);
    ol::execution_preservation(eq,lib,programs,source,labels);
    if labels.len()>0 {
        let prefix=source.drop_last();let previous=labels.drop_last();
        assert(g::execution(lib,programs,prefix,previous)) by {
            assert forall|i:int| 0<=i<previous.len() implies g::step(lib,programs,prefix[i],prefix[i+1],previous[i].0,previous[i].1) by {}
        }
        suffix_transport(eq,h,lib,programs,prefix,previous,start);
        let moved=transport(lib,programs,prefix,previous,start);
        step_transport(eq,h,lib,programs,prefix.last(),source.last(),moved.last(),labels.last().0,labels.last().1);
        let result=transport(lib,programs,source,labels,start);
        let tail=successor(lib,programs,prefix.last(),source.last(),moved.last(),labels.last().0,labels.last().1);
        assert(prefix.last()==source[source.len()-2]);assert(result==moved.push(tail));
        assert(result.len()==labels.len()+1);
        assert(g::step(lib,programs,moved.last(),tail,labels.last().0,labels.last().1));
        assert(g::execution(lib,programs,result,labels)) by {
            assert forall|i:int| 0<=i<labels.len() implies g::step(lib,programs,result[i],result[i+1],labels[i].0,labels[i].1) by {
                if i<previous.len() {
                    assert(result[i]==moved[i]);assert(result[i+1]==moved[i+1]);assert(labels[i]==previous[i]);
                    assert(g::step(lib,programs,moved[i],moved[i+1],previous[i].0,previous[i].1));
                } else {assert(i==labels.len()-1);assert(result[i]==moved.last());assert(result[i+1]==tail);assert(labels[i]==labels.last());}
            }
        }
        assert forall|i:int| 0<=i<source.len() implies related(eq,h,source[i],result[i]) && g::well_formed(lib,programs,result[i]) by {
            if i<prefix.len() {assert(source[i]==prefix[i]);assert(result[i]==moved[i]);}
            else {assert(i==source.len()-1);assert(result[i]==tail);}
        }
    } else {assert(source.len()==1);}
}

/// Historical admissibility is derived from the component membership at each
/// actual landing, including entries no longer referenced by a live journal.
pub open spec fn permitted_history<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,history:Seq<g::Entry<U,I>>)->bool {
    forall|i:int| #![trigger history[i]] 0<=i<history.len() ==> {
        let e=history[i];let actor=g::owner(e.landed.receipt);
        crate::mixed_syntax::permitted(lib,dep::declarations(e.input,actor),e.input.control.fibers[actor].provisions,programs(actor)(e.iterator))
    }
}
pub proof fn permitted_step<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),permitted_history(lib,programs,a.history),g::step(lib,programs,a,z,actor,rule),
    ensures permitted_history(lib,programs,z.history),
{
    ol::frame(eq,lib,programs,a,z,actor,rule);
    if g::landing(a,z,rule) {
        ol::run_members(eq,lib,programs,a.state,actor,a.current[actor].unwrap());
        assert forall|i:int| #![trigger z.history[i]] 0<=i<z.history.len() implies {
            let e=z.history[i];let n=g::owner(e.landed.receipt);
            crate::mixed_syntax::permitted(lib,dep::declarations(e.input,n),e.input.control.fibers[n].provisions,programs(n)(e.iterator))
        } by {if i<a.history.len() {assert(z.history[i]==a.history[i]);} else {assert(i==a.history.len());assert(z.history[i]==g::entry(lib,programs,a,actor));}}
    }
}
pub proof fn history_from_empty<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires og::primitive_theory(eq,lib),g::execution(lib,programs,source,labels),source.first()==g::empty::<U,I>(),
    ensures g::well_formed(lib,programs,source.last()),permitted_history(lib,programs,source.last().history),
    decreases labels.len(),
{
    g::empty_well_formed(lib,programs);ol::execution_preservation(eq,lib,programs,source,labels);
    if labels.len()>0 {
        let prefix=source.drop_last();let previous=labels.drop_last();
        assert(g::execution(lib,programs,prefix,previous)) by {
            assert forall|i:int| 0<=i<previous.len() implies g::step(lib,programs,prefix[i],prefix[i+1],previous[i].0,previous[i].1) by {}
        }
        history_from_empty(eq,lib,programs,prefix,previous);
        permitted_step(eq,lib,programs,prefix.last(),source.last(),labels.last().0,labels.last().1);
    } else {assert(source.len()==1);}
}
pub proof fn history_reflexive<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,history:Seq<g::Entry<U,I>>,i:int)
    requires og::primitive_theory(eq,lib),permitted_history(lib,programs,history),g::history_sound(lib,programs,history),0<=i<history.len(),
    ensures obs::receipt_related(eq,history[i].landed.receipt,history[i].landed.receipt),
{
    let e=history[i];let actor=g::owner(e.landed.receipt);
    obs::actual_receipt_reflexive(eq,lib,programs(actor)(e.iterator),e.input,actor);
}
pub proof fn old_tokens(h:nat,stack:Seq<nat>)
    requires forall|i:int| 0<=i<stack.len() ==> #[trigger] stack[i]<h,
    ensures tokens(h,stack)==stack,
{
    assert(tokens(h,stack) =~= stack);
}

/// The actual Iter/Iter diamond creates exactly the initial relation used by
/// suffix transport. Earlier permitted receipts are respected by the primitive
/// theory; the swapped pair uses the two actual returned inverse functions.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn iteration_related<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,b:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,other:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),permitted_history(lib,programs,a.history),actor!=other,
        g::step(lib,programs,a,b,actor,r::Rule::Iter),g::step(lib,programs,b,z,other,r::Rule::Iter),
        ix::operational(programs(actor)(a.current[actor].unwrap())),ix::operational(programs(other)(a.current[other].unwrap())),
        ix::pair_independent(eq,lib,ix::node(programs(actor)(a.current[actor].unwrap())),ix::node(programs(other)(a.current[other].unwrap()))),
    ensures related(eq,a.history.len(),z,ix::last_reversed(lib,programs,a,actor,other)),
        g::well_formed(lib,programs,z),g::well_formed(lib,programs,ix::last_reversed(lib,programs,a,actor,other)),
        g::step(lib,programs,a,ix::first_reversed(lib,programs,a,other),other,r::Rule::Iter),
        g::step(lib,programs,ix::first_reversed(lib,programs,a,other),ix::last_reversed(lib,programs,a,actor,other),actor,r::Rule::Iter),
{
    ix::diamond(eq,lib,programs,a,b,z,actor,other);
    let mid=ix::first_reversed(lib,programs,a,other);let last=ix::last_reversed(lib,programs,a,actor,other);let h=a.history.len();
    ol::configuration_preservation(eq,lib,programs,a,b,actor,r::Rule::Iter);
    ol::configuration_preservation(eq,lib,programs,b,z,other,r::Rule::Iter);
    ix::iter_frame(lib,programs,a,b,actor);ix::iter_frame(lib,programs,b,z,other);
    ix::iter_frame(lib,programs,a,mid,other);ix::iter_frame(lib,programs,mid,last,actor);
    obs::projection_to_tables(eq,z.state,last.state);
    obs::projected_receipts(eq,z.history[h as int].landed.receipt,last.history[h as int+1].landed.receipt);
    obs::projected_receipts(eq,z.history[h as int+1].landed.receipt,last.history[h as int].landed.receipt);
    assert(z.state.effects =~= last.state.effects) by {
        assert forall|id:usize| z.state.effects.dom().contains(id) implies z.state.effects[id]==last.state.effects[id] by {assert(s::registered(z.state,id));}
    }
    assert(z.state.iterators =~= last.state.iterators) by {
        assert forall|id:usize| z.state.iterators.dom().contains(id) implies z.state.iterators[id]==last.state.iterators[id] by {assert(s::registered(z.state,id));}
    }
    assert forall|id:usize| z.state.accumulators.dom().contains(id) implies last.state.accumulators[id]==tokens(h,z.state.accumulators[id]) by {
        assert(s::registered(a.state,id));
        assert forall|i:int| 0<=i<a.state.accumulators[id].len() implies a.state.accumulators[id][i]<h by {}
        old_tokens(h,a.state.accumulators[id]);
        tokens_laws(h,a.state.accumulators[id],h);tokens_laws(h,a.state.accumulators[id],h+1);
    }
    assert forall|i:nat| #![trigger z.history[i as int]] i<z.history.len() implies {
        let x=z.history[i as int];let y=last.history[token(h,i) as int];
        &&& x.iterator==y.iterator && x.landed.next==y.landed.next && x.landed.spawn==y.landed.spawn
        &&& obs::receipt_related(eq,x.landed.receipt,y.landed.receipt)
    } by {
        if i<h {history_reflexive(eq,lib,programs,a.history,i as int);assert(token(h,i)==i);}
        else if i==h {
            assert(z.history[i as int]==g::entry(lib,programs,a,actor));
            assert(last.history[h as int+1]==g::entry(lib,programs,mid,actor));
        } else {
            assert(i==h+1);assert(z.history[i as int]==g::entry(lib,programs,b,other));
            assert(last.history[h as int]==g::entry(lib,programs,a,other));
        }
    }
}

/// A finite actual prefix from empty discharges all old-history admissibility.
/// Every given legal continuation, across all nine rules, is then constructed
/// after the reversed pair. No legality or inverse success of that new suffix
/// is an input to this theorem.
pub proof fn iteration_suffix<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    prefix:Seq<g::Configuration<U,I>>,before:Seq<(usize,r::Rule)>,b:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,other:usize,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires og::primitive_theory(eq,lib),g::execution(lib,programs,prefix,before),prefix.first()==g::empty::<U,I>(),actor!=other,
        g::step(lib,programs,prefix.last(),b,actor,r::Rule::Iter),g::step(lib,programs,b,z,other,r::Rule::Iter),
        ix::operational(programs(actor)(prefix.last().current[actor].unwrap())),ix::operational(programs(other)(prefix.last().current[other].unwrap())),
        ix::pair_independent(eq,lib,ix::node(programs(actor)(prefix.last().current[actor].unwrap())),ix::node(programs(other)(prefix.last().current[other].unwrap()))),
        g::execution(lib,programs,source,labels),source.first()==z,
    ensures {
        let a=prefix.last();let middle=ix::first_reversed(lib,programs,a,other);let last=ix::last_reversed(lib,programs,a,actor,other);
        let moved=transport(lib,programs,source,labels,last);let h=a.history.len();
        &&& g::step(lib,programs,a,middle,other,r::Rule::Iter) && g::step(lib,programs,middle,last,actor,r::Rule::Iter)
        &&& moved.first()==last && moved.len()==source.len() && g::execution(lib,programs,moved,labels)
        &&& forall|i:int| 0<=i<source.len() ==> related(eq,h,source[i],moved[i]) && g::well_formed(lib,programs,moved[i])
            && crate::partial_independence::context_eq(eq)(crate::projection::project(source[i].state,ISet::full()),crate::projection::project(moved[i].state,ISet::full()))
    },
{
    history_from_empty(eq,lib,programs,prefix,before);
    let a=prefix.last();iteration_related(eq,lib,programs,a,b,z,actor,other);
    let last=ix::last_reversed(lib,programs,a,actor,other);
    suffix_transport(eq,a.history.len(),lib,programs,source,labels,last);
    ol::execution_preservation(eq,lib,programs,source,labels);
    let moved=transport(lib,programs,source,labels,last);
    assert forall|i:int| 0<=i<source.len() implies related(eq,a.history.len(),source[i],moved[i]) && g::well_formed(lib,programs,moved[i])
        && crate::partial_independence::context_eq(eq)(crate::projection::project(source[i].state,ISet::full()),crate::projection::project(moved[i].state,ISet::full())) by {
        obs::tables_to_projection(eq,source[i].state,moved[i].state);
    }
}

#[verifier::opaque]
pub open spec fn example_suffix()->Seq<g::Configuration<int,ix::ExampleStage>> {
    let z=ix::example_trace().last();
    let a=g::Configuration {state:s::with_control(z.state,global::retire_fiber(z.state.control,1)),..z};
    let b=g::edit(a,1,Phase::Unloading,ix::example_view(),None,a.state.accumulators[1usize]);
    let c=g::unload(b,1);
    let d=g::Configuration {state:s::with_control(c.state,global::retire_fiber(c.state.control,2)),..c};
    let e=g::edit(d,2,Phase::Unloading,ix::example_view(),None,d.state.accumulators[2usize]);
    let f=g::unload(e,2);
    seq![z,a,b,c,d,e,f]
}
pub open spec fn example_suffix_labels()->Seq<(usize,r::Rule)> {
    seq![(1usize,r::Rule::Retire),(1usize,r::Rule::Divert),(1usize,r::Rule::Unload),
        (2usize,r::Rule::Retire),(2usize,r::Rule::Divert),(2usize,r::Rule::Unload)]
}

/// Actual nonempty operation journals are consumed after the exchange. Both
/// schedules restore provider 0 from 15 through 13 to 10, using each schedule's
/// own recorded receipts and differently numbered tokens.
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub proof fn shared_provider_cleanup()
    ensures {
        let lib=crate::recovery_examples::library();let programs=ix::example_programs();let eq=crate::recovery_examples::equality();
        let prefix=ix::example_trace().subrange(0,8);let end=ix::last_reversed(lib,programs,prefix.last(),1,2);
        let source=example_suffix();let moved=transport(lib,programs,source,example_suffix_labels(),end);
        &&& g::execution(lib,programs,source,example_suffix_labels()) && g::execution(lib,programs,moved,example_suffix_labels())
        &&& source[0].state.tables[0usize][ix::example_key()]==15
        &&& source[3].state.tables[0usize][ix::example_key()]==13 && moved[3].state.tables[0usize][ix::example_key()]==13
        &&& source.last().state.tables[0usize][ix::example_key()]==10 && moved.last().state.tables[0usize][ix::example_key()]==10
        &&& source.last().state.accumulators[1usize].len()==0 && source.last().state.accumulators[2usize].len()==0
        &&& moved.last().state.accumulators[1usize].len()==0 && moved.last().state.accumulators[2usize].len()==0
        &&& source[0].state.accumulators[1usize]==seq![1nat] && end.state.accumulators[1usize]==seq![2nat]
        &&& source[0].state.accumulators[2usize]==seq![2nat] && end.state.accumulators[2usize]==seq![1nat]
        &&& forall|i:int| 0<=i<moved.len() ==> related(eq,1,source[i],moved[i]) && g::well_formed(lib,programs,moved[i])
    },
{
    ix::example_execution();ix::shared_provider();crate::recovery_examples::primitive_theory();ix::translations_independent(2,3);
    let lib=crate::recovery_examples::library();let programs=ix::example_programs();let eq=crate::recovery_examples::equality();
    og::exact_theory(eq,lib);reveal(ix::example_trace);reveal(example_suffix);
    let trace=ix::example_trace();let prefix=trace.subrange(0,8);let before=ix::example_labels().subrange(0,7);
    let source=example_suffix();let labels=example_suffix_labels();
    ix::example_resolve(trace[7].state,1);ix::example_resolve(trace[8].state,2);
    reveal_with_fuel(g::restore,2);
    assert(g::execution(lib,programs,prefix,before)) by {
        assert forall|i:int| 0<=i<before.len() implies g::step(lib,programs,prefix[i],prefix[i+1],before[i].0,before[i].1) by {}
    }
    assert(g::step(lib,programs,source[0],source[1],1,r::Rule::Retire));
    assert(g::step(lib,programs,source[1],source[2],1,r::Rule::Divert));
    ix::example_resolve(source[2].state,1);
    assert(g::restore(source[2].history,source[2].state.accumulators[1usize],source[2].state,1).is_some());
    assert(!r::relied(source[2].state.control,1));
    assert(g::step(lib,programs,source[2],source[3],1,r::Rule::Unload));
    assert(g::step(lib,programs,source[3],source[4],2,r::Rule::Retire));
    assert(g::step(lib,programs,source[4],source[5],2,r::Rule::Divert));
    ix::example_resolve(source[5].state,2);
    assert(g::restore(source[5].history,source[5].state.accumulators[2usize],source[5].state,2).is_some());
    assert(!r::relied(source[5].state.control,2));
    assert(g::step(lib,programs,source[5],source[6],2,r::Rule::Unload));
    assert(g::execution(lib,programs,source,labels)) by {
        assert forall|i:int| 0<=i<labels.len() implies g::step(lib,programs,source[i],source[i+1],labels[i].0,labels[i].1) by {
            if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else {assert(i==5);}
        }
    }
    iteration_suffix(eq,lib,programs,prefix,before,trace[8],trace[9],1,2,source,labels);
    let end=ix::last_reversed(lib,programs,prefix.last(),1,2);let moved=transport(lib,programs,source,labels,end);
    assert(source.len()==7);assert(moved.len()==7);
    assert(related(eq,1,source[3],moved[3]));assert(related(eq,1,source.last(),moved.last()));
}

} // verus!
