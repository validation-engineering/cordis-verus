//! Constructed shared-key episode deletion with actual foreign Unloads.
//!
//! Source and target histories retain their own authentic returned receipts.
//! Only new owner entries are omitted; surviving tokens are compressed, and
//! related partial inverses transport strict domains into the target restore.
//!
//! The theorem covers a fixed registry, operational Unit/Operation landings,
//! an initially inactive owner with no provisions, and foreign unload journals
//! minted within this trace segment. Existing authentic history is retained.
//! Initial live journals, Child/Provision landings and registry edits remain
//! outside this fragment. History authenticity follows from the constructed
//! well-formed execution, not from the standalone restore transport helper.
#[cfg(verus_keep_ghost)]
use crate::{
    calculus as c, dependent_grammar as d, dependent_lift as dep, foreign_unload as fu,
    grammar_lift as lift, mediated as m, mixed_grammar as g, mixed_iteration_exchange as ix,
    mixed_observational_runs as obs, observational_grammar as og, observational_lift as ol,
    partial_independence as pi, preservation as inv, projection as p, recovery_examples as ex,
    refinement as r, semantics as s, shared_execution as sh, shared_replay as replay,
    strict_journal as sj, Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {

#[verifier::opaque]
pub open spec fn index<U,I>(history:Seq<g::Entry<U,I>>,offset:nat,owner:usize,token:nat)->nat
    decreases token,
{
    if token<=offset {token} else {
        index(history,offset,owner,(token-1) as nat)+if g::owner(history[token as int-1].landed.receipt)==owner {0nat}else{1nat}
    }
}
pub open spec fn rename<U,I>(history:Seq<g::Entry<U,I>>,offset:nat,owner:usize,tokens:Seq<nat>)->Seq<nat> {
    tokens.map(|_i:int,t:nat|index(history,offset,owner,t))
}
pub proof fn index_append<U,I>(history:Seq<g::Entry<U,I>>,entry:g::Entry<U,I>,offset:nat,owner:usize,token:nat)
    requires token<=history.len(),
    ensures index(history.push(entry),offset,owner,token)==index(history,offset,owner,token),
    decreases token,
{
    reveal(index);
    if token>offset {index_append(history,entry,offset,owner,(token-1) as nat);assert(history.push(entry)[token as int-1]==history[token as int-1]);}
}
pub proof fn rename_laws<U,I>(history:Seq<g::Entry<U,I>>,offset:nat,owner:usize,tokens:Seq<nat>,fresh:nat)
    ensures rename(history,offset,owner,tokens.push(fresh))==rename(history,offset,owner,tokens).push(index(history,offset,owner,fresh)),
        rename(history,offset,owner,Seq::empty())==Seq::<nat>::empty(),
        tokens.len()>0 ==> rename(history,offset,owner,tokens).last()==index(history,offset,owner,tokens.last())
            && rename(history,offset,owner,tokens).drop_last()==rename(history,offset,owner,tokens.drop_last()),
{
    assert(rename(history,offset,owner,tokens.push(fresh)) =~= rename(history,offset,owner,tokens).push(index(history,offset,owner,fresh)));
    if tokens.len()>0 {assert(rename(history,offset,owner,tokens).drop_last() =~= rename(history,offset,owner,tokens.drop_last()));}
}
pub proof fn rename_append<U,I>(history:Seq<g::Entry<U,I>>,entry:g::Entry<U,I>,offset:nat,owner:usize,tokens:Seq<nat>)
    requires forall|i:int| 0<=i<tokens.len() ==> tokens[i]<=history.len(),
    ensures rename(history.push(entry),offset,owner,tokens)==rename(history,offset,owner,tokens),
{
    assert(rename(history.push(entry),offset,owner,tokens) =~= rename(history,offset,owner,tokens)) by {
        assert forall|i:int| 0<=i<tokens.len() implies rename(history.push(entry),offset,owner,tokens)[i]==rename(history,offset,owner,tokens)[i] by {
            index_append(history,entry,offset,owner,tokens[i]);
        }
    }
}
pub open spec fn histories<U,I>(eq:spec_fn(Port,U,U)->bool,left:Seq<g::Entry<U,I>>,right:Seq<g::Entry<U,I>>,offset:nat,owner:usize)->bool {
    &&& offset<=left.len() && offset<=right.len() && right.len()==index(left,offset,owner,left.len())
    &&& forall|i:int| 0<=i<offset ==> right[i]==left[i]
    &&& forall|i:int| #![trigger left[i]] offset<=i<left.len() && g::owner(left[i].landed.receipt)!=owner ==> {
        let at=index(left,offset,owner,i as nat);let old=left[i];let new=right[at as int];
        &&& at<right.len() && old.iterator==new.iterator && old.landed.next==new.landed.next && old.landed.spawn==new.landed.spawn
        &&& obs::receipt_related(eq,old.landed.receipt,new.landed.receipt)
    }
}
pub open spec fn related<U,I>(eq:spec_fn(Port,U,U)->bool,left:g::Configuration<U,I>,right:g::Configuration<U,I>,offset:nat,owner:usize)->bool {
    &&& sh::controls(left,right,owner) && histories(eq,left.history,right.history,offset,owner)
    &&& forall|actor:usize| s::registered(left.state,actor) && actor!=owner ==> right.state.accumulators[actor]==rename(left.history,offset,owner,left.state.accumulators[actor])
}
pub proof fn histories_push<U,I>(eq:spec_fn(Port,U,U)->bool,left:Seq<g::Entry<U,I>>,right:Seq<g::Entry<U,I>>,old:g::Entry<U,I>,new:g::Entry<U,I>,offset:nat,owner:usize)
    requires histories(eq,left,right,offset,owner),g::owner(old.landed.receipt)!=owner,old.iterator==new.iterator,old.landed.next==new.landed.next,
        old.landed.spawn==new.landed.spawn,obs::receipt_related(eq,old.landed.receipt,new.landed.receipt),
    ensures histories(eq,left.push(old),right.push(new),offset,owner),
{
    reveal(index);
    index_append(left,old,offset,owner,left.len());
    assert forall|i:int| 0<=i<offset implies right.push(new)[i]==left.push(old)[i] by {}
    assert forall|i:int| #![trigger left.push(old)[i]] offset<=i<left.push(old).len() && g::owner(left.push(old)[i].landed.receipt)!=owner implies {
        let at=index(left.push(old),offset,owner,i as nat);let x=left.push(old)[i];let y=right.push(new)[at as int];
        &&& at<right.push(new).len() && x.iterator==y.iterator && x.landed.next==y.landed.next && x.landed.spawn==y.landed.spawn
        &&& obs::receipt_related(eq,x.landed.receipt,y.landed.receipt)
    } by {
        index_append(left,old,offset,owner,i as nat);
        if i<left.len() {assert(left.push(old)[i]==left[i]);assert(index(left,offset,owner,i as nat)<right.len());}
        else {assert(i==left.len());assert(index(left,offset,owner,i as nat)==right.len());}
    }
}
pub proof fn histories_skip<U,I>(eq:spec_fn(Port,U,U)->bool,left:Seq<g::Entry<U,I>>,right:Seq<g::Entry<U,I>>,old:g::Entry<U,I>,offset:nat,owner:usize)
    requires histories(eq,left,right,offset,owner),g::owner(old.landed.receipt)==owner,
    ensures histories(eq,left.push(old),right,offset,owner),
{
    reveal(index);
    index_append(left,old,offset,owner,left.len());
    assert forall|i:int| #![trigger left.push(old)[i]] offset<=i<left.push(old).len() && g::owner(left.push(old)[i].landed.receipt)!=owner implies {
        let at=index(left.push(old),offset,owner,i as nat);let x=left.push(old)[i];let y=right[at as int];
        &&& at<right.len() && x.iterator==y.iterator && x.landed.next==y.landed.next && x.landed.spawn==y.landed.spawn
        &&& obs::receipt_related(eq,x.landed.receipt,y.landed.receipt)
    } by {assert(i<left.len());index_append(left,old,offset,owner,i as nat);assert(left.push(old)[i]==left[i]);}
}
pub proof fn initial_related<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,owner:usize,eq:spec_fn(Port,U,U)->bool)
    requires g::well_formed(lib,programs,a),s::registered(a.state,owner),a.state.control.fibers[owner].phase==Phase::Inactive,a.state.control.fibers[owner].provisions.is_empty(),
    ensures related(eq,a,a,a.history.len(),owner),
{
    reveal(index);
    sh::initial_controls(lib,programs,a,owner);
    assert forall|actor:usize| s::registered(a.state,actor) && actor!=owner implies a.state.accumulators[actor]==rename(a.history,a.history.len(),owner,a.state.accumulators[actor]) by {
        assert(a.state.accumulators[actor] =~= rename(a.history,a.history.len(),owner,a.state.accumulators[actor])) by {
            assert forall|i:int| 0<=i<a.state.accumulators[actor].len() implies a.state.accumulators[actor][i]==rename(a.history,a.history.len(),owner,a.state.accumulators[actor])[i] by {
                assert(a.state.accumulators[actor][i]<a.history.len());
            }
        }
    }
}

pub open spec fn simple<U>(receipt:g::Receipt<U>)->bool {
    match receipt {g::Receipt::Table {receipt}=>match receipt.inverse {lift::Inverse::Unit|lift::Inverse::Operation {..}=>true,_=>false},_=>false}
}
pub proof fn historical_simple<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,entry:g::Entry<U,I>)
    requires fu::historical(lib,programs,entry),
    ensures simple(entry.landed.receipt),
{ }
pub proof fn flat_related<U>(eq:spec_fn(Port,U,U)->bool,left:g::Receipt<U>,right:g::Receipt<U>)
    requires simple(left),obs::receipt_related(eq,left,right),
    ensures simple(right),m::partial_related(pi::context_eq(eq),sh::flat(left),sh::flat(right)),
{
    if let g::Receipt::Table {receipt:a}=left {if let g::Receipt::Table {receipt:b}=right {
        if let lift::Inverse::Operation {key,undo:f,..}=a.inverse {if let lift::Inverse::Operation {undo:h,..}=b.inverse {
            m::inverse_lift_respects(eq,ISet::full(),key,f,h);
        }}
    }}
}
pub proof fn pin_transport<U>(left:g::Receipt<U>,right:g::Receipt<U>,a:s::State<U>,b:s::State<U>,actor:usize,eq:spec_fn(Port,U,U)->bool)
    requires simple(left),obs::receipt_related(eq,left,right),g::owner(left)==actor,g::undo(left,a).is_some(),
        s::registered(b,actor),a.control.fibers[actor]==b.control.fibers[actor],
    ensures sh::pinned(right,b,actor),
{
    if let g::Receipt::Table {receipt:x}=left {if let g::Receipt::Table {receipt:y}=right {
        if let lift::Inverse::Operation {key,..}=x.inverse {assert(lift::resolve(a,actor,key)==lift::resolve(b,actor,key));}
    }}
}

pub proof fn one_inverse<U>(eq:spec_fn(Port,U,U)->bool,left:g::Receipt<U>,right:g::Receipt<U>,source:s::State<U>,target:s::State<U>,actor:usize,reference:IMap<Port,U>)
    requires inv::well_formed(source),inv::well_formed(target),s::registered(target,actor),source.control.fibers[actor]==target.control.fibers[actor],
        simple(left),obs::receipt_related(eq,left,right),g::owner(left)==actor,g::undo(left,source).is_some(),
        sh::flat(left)(reference).is_some(),pi::context_eq(eq)(reference,p::project(target,ISet::full())),
    ensures {
        let a=g::undo(left,source).unwrap();let b=g::undo(right,target).unwrap();
        &&& g::undo(right,target).is_some() && inv::well_formed(a) && inv::well_formed(b)
        &&& a.control==source.control && b.control==target.control
        &&& forall|n:usize| s::registered(target,n) ==> b.tables[n].dom()==target.tables[n].dom()
        &&& pi::context_eq(eq)(sh::flat(left)(reference).unwrap(),p::project(b,ISet::full()))
    },
{
    flat_related(eq,left,right);pin_transport(left,right,source,target,actor,eq);
    sh::inverse_definedness(right,target,actor);fu::table_inverse_projects(left,source);
    if let g::Receipt::Table {receipt}=left {lift::undo_preservation(receipt,source);}
}

/// Counterfactual values are used only to prove the real target's inverse
/// definedness. Every target restore still uses its own authentic receipt.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn restore_transport<U,I>(eq:spec_fn(Port,U,U)->bool,
    left:Seq<g::Entry<U,I>>,right:Seq<g::Entry<U,I>>,tokens:Seq<nat>,offset:nat,owner:usize,actor:usize,source:s::State<U>,target:s::State<U>,reference:IMap<Port,U>)
    requires actor!=owner,inv::well_formed(source),inv::well_formed(target),s::registered(target,actor),source.control.fibers[actor]==target.control.fibers[actor],
        histories(eq,left,right,offset,owner),fu::tracked_tokens(left,tokens,offset,actor),g::restore(left,tokens,source,actor).is_some(),
        forall|i:int| offset<=i<left.len() ==> simple(#[trigger] left[i].landed.receipt),
        pi::run(sh::receipt_word(left,tokens),reference).is_some(),pi::context_eq(eq)(reference,p::project(target,ISet::full())),
    ensures {
        let out=g::restore(right,rename(left,offset,owner,tokens),target,actor);
        &&& out.is_some() && inv::well_formed(out.unwrap()) && out.unwrap().control==target.control
        &&& forall|n:usize| s::registered(target,n) ==> out.unwrap().tables[n].dom()==target.tables[n].dom()
        &&& pi::context_eq(eq)(pi::run(sh::receipt_word(left,tokens),reference).unwrap(),p::project(out.unwrap(),ISet::full()))
    },
    decreases tokens.len(),
{
    rename_laws(left,offset,owner,tokens,0);
    if tokens.len()>0 {
        let old=tokens.last();let new=index(left,offset,owner,old);let a=left[old as int].landed.receipt;let b=right[new as int].landed.receipt;
        assert(offset<=old<left.len());assert(g::owner(a)==actor);assert(obs::receipt_related(eq,a,b));
        assert(simple(a));
        sj::run_prepend(sh::flat(a),sh::receipt_word(left,tokens.drop_last()),reference);
        one_inverse(eq,a,b,source,target,actor,reference);
        let target_after=g::undo(b,target).unwrap();let source_after=g::undo(a,source).unwrap();
        let after=sh::flat(a)(reference).unwrap();
        restore_transport(eq,left,right,tokens.drop_last(),offset,owner,actor,source_after,target_after,after);
        assert forall|n:usize| s::registered(target,n) implies g::restore(right,rename(left,offset,owner,tokens),target,actor).unwrap().tables[n].dom()==target.tables[n].dom() by {
            assert(s::registered(target_after,n));
        }
    }
}

/// The abstract sequence of foreign inverse events is exactly this strict
/// receipt word. It is not a second lifecycle trace or an identity extension.
pub proof fn foreign_inverse_word<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,history:Seq<g::Entry<U,I>>,tokens:Seq<nat>,offset:nat,owner:usize,actor:usize,
    prefix:Seq<fu::Action<IMap<Port,U>>>,initial:IMap<Port,U>)
    requires offset<=history.len(),fu::tracked_tokens(history,tokens,offset,actor),fu::catalog(prefix)==fu::fresh_records(lib,programs,history,offset,owner),
        sj::foreign(fu::events(prefix),initial).is_some(),
    ensures sj::foreign(fu::events(prefix+fu::inverse_actions(tokens,offset)),initial)==pi::run(sh::receipt_word(history,tokens),sj::foreign(fu::events(prefix),initial).unwrap()),
    decreases tokens.len(),
{
    if tokens.len()==0 {assert(prefix+fu::inverse_actions::<IMap<Port,U>>(tokens,offset) =~= prefix);}
    else {
        let old=tokens.last();let at=(old-offset) as nat;let action=fu::Action::Inverse {token:at};let next=prefix.push(action);
        assert(offset<=old<history.len());assert(fu::catalog(prefix)[at as int]==fu::entry_pair(lib,programs,history[old as int],owner));
        assert(next.drop_last() =~= prefix);assert(fu::events(next).drop_last() =~= fu::events(prefix));
        let input=sj::foreign(fu::events(prefix),initial).unwrap();let value=sh::flat(history[old as int].landed.receipt)(input);
        assert(sj::foreign(fu::events(next),initial)==value);
        sj::run_prepend(sh::flat(history[old as int].landed.receipt),sh::receipt_word(history,tokens.drop_last()),input);
        if value.is_some() {foreign_inverse_word(lib,programs,history,tokens.drop_last(),offset,owner,actor,next,initial);}
        else {
            // Strict failed prefixes remain failed after any suffix.
            foreign_failure(next,fu::inverse_actions::<IMap<Port,U>>(tokens.drop_last(),offset),initial);
        }
        assert(next+fu::inverse_actions::<IMap<Port,U>>(tokens.drop_last(),offset) =~= prefix+fu::inverse_actions::<IMap<Port,U>>(tokens,offset));
    }
}
pub proof fn foreign_failure<S>(prefix:Seq<fu::Action<S>>,suffix:Seq<fu::Action<S>>,initial:S)
    requires sj::foreign(fu::events(prefix),initial).is_none(),
    ensures sj::foreign(fu::events(prefix+suffix),initial).is_none(),
    decreases suffix.len(),
{
    if suffix.len()==0 {assert(prefix+suffix =~= prefix);}
    else {
        foreign_failure(prefix,suffix.drop_last(),initial);
        assert((prefix+suffix).drop_last() =~= prefix+suffix.drop_last());
        assert(fu::events(prefix+suffix).drop_last() =~= fu::events(prefix+suffix.drop_last()));
    }
}

pub proof fn stable_pending<A,X,U,B,I,J>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize,
    node:dep::Node<A,X,U,B,J>,actor:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),
        fu::fragment(programs,source,labels,source.first().history.len(),owner),replay::operational(node),dep::run(lib,node,source.last().state,actor).is_some(),
        d::permitted(lib,dep::declarations(source.last().state,actor),source.last().state.control.fibers[actor].provisions,node),
    ensures forall|i:int| 0<=i<sj::journal(fu::events(fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner))).len()
        ==> pi::stable(eq,dep::stage(lib,node),#[trigger] sj::journal(fu::events(fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner)))[i]),
{
    fu::actual_source(eq,lib,programs,source,labels,owner);fu::fresh_historical(eq,lib,programs,source,labels);
    let offset=source.first().history.len();let actions=fu::trace_actions(lib,programs,source,labels,offset,owner);let records=fu::catalog(actions);let word=sj::journal(fu::events(actions));
    fu::journal_origins(actions);
    assert forall|i:int| 0<=i<word.len() implies pi::stable(eq,dep::stage(lib,node),#[trigger] word[i]) by {
        let j=choose|j:int| 0<=j<records.len() && records[j].own && records[j].inverse==word[i];
        let entry=source.last().history[offset as int+j];let old_actor=g::owner(entry.landed.receipt);let old_node=replay::dependent(programs(old_actor)(entry.iterator));
        assert(fu::historical(lib,programs,entry));assert(records[j]==fu::entry_pair(lib,programs,entry,owner));
        replay::call_independence(eq,lib,old_node,node,entry.input,source.last().state,old_actor,actor);
    }
}
pub proof fn actual_names<A,X,U,B,I>(lib:g::Library<A,X,U,B>,node:dep::Node<A,X,U,B,I>,a:s::State<U>,b:s::State<U>,actor:usize)
    requires dep::run(lib,node,a,actor).is_some(),dep::run(lib,node,b,actor).is_some(),a.control.fibers[actor]==b.control.fibers[actor],
    ensures ix::receipt_names(dep::run(lib,node,a,actor).unwrap().receipt,dep::run(lib,node,b,actor).unwrap().receipt),
{
    if let d::Node::Operation {operation,..}=node {assert(lift::resolve(a,actor,(lib.key)(operation))==lift::resolve(b,actor,(lib.key)(operation)));}
}

/// Generalize the real foreign call bridge to prefixes containing authentic
/// foreign Unloads. Stable raw outcomes retain the original arbitrary-I next.
#[verifier::spinoff_prover]
pub proof fn next_call<A,X,U,B,I,J>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize,
    node:dep::Node<A,X,U,B,J>,target:s::State<U>,actor:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),
        fu::fragment(programs,source,labels,source.first().history.len(),owner),actor!=owner,inv::well_formed(target),s::registered(target,actor),target.control.fibers[actor].phase!=Phase::Inactive,
        source.last().state.control.fibers[actor]==target.control.fibers[actor],replay::operational(node),dep::run(lib,node,source.last().state,actor).is_some(),
        d::permitted(lib,dep::declarations(source.last().state,actor),source.last().state.control.fibers[actor].provisions,node),
        pi::context_eq(eq)(sj::foreign(fu::events(fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner)),p::project(source.first().state,ISet::full())).unwrap(),p::project(target,ISet::full())),
    ensures {
        let old=dep::run(lib,node,source.last().state,actor).unwrap();let new=dep::run(lib,node,target,actor).unwrap();
        let es=fu::events(fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner));let initial=p::project(source.first().state,ISet::full());let e=replay::call_event(lib,node,source.last().state,actor,false);
        &&& dep::run(lib,node,target,actor).is_some() && new.next==old.next
        &&& obs::receipt_related(eq,g::Receipt::Table {receipt:old.receipt},g::Receipt::Table {receipt:new.receipt})
        &&& (e.forward)(sj::foreign(es,initial).unwrap()).is_some()
        &&& pi::context_eq(eq)((e.forward)(sj::foreign(es,initial).unwrap()).unwrap(),p::project(new.state,ISet::full()))
    },
{
    fu::actual_foreign_unload_recovery(eq,lib,programs,source,labels,owner);replay::context_equivalence(eq,lib);fu::fresh_historical(eq,lib,programs,source,labels);
    let es=fu::events(fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner));let initial=p::project(source.first().state,ISet::full());let word=sj::journal(es);let a=source.last().state;
    stable_pending(eq,lib,programs,source,labels,owner,node,actor);
    assert(pi::context_eq(eq)(pi::run(word,p::project(a,ISet::full())).unwrap(),p::project(target,ISet::full())));
    replay::run_after_word(eq,lib,node,a,target,actor,word);actual_names(lib,node,a,target,actor);
    let left=g::Receipt::Table {receipt:dep::run(lib,node,a,actor).unwrap().receipt};let right=g::Receipt::Table {receipt:dep::run(lib,node,target,actor).unwrap().receipt};
    obs::projected_receipts(eq,left,right);
    replay::call_contract(eq,lib,node,a,actor,false);lift::run_projects(dep::stage(lib,node),target,actor);
    let e=replay::call_event(lib,node,a,actor,false);assert((e.forward)(p::project(target,ISet::full())).is_some());
    assert((e.forward)(sj::foreign(es,initial).unwrap()).is_some());
}

pub open spec fn advance<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:g::Configuration<U,I>,next:g::Configuration<U,I>,target:g::Configuration<U,I>,actor:usize,rule:r::Rule,owner:usize)->g::Configuration<U,I> {
    if rule==r::Rule::Unload && actor!=owner {g::unload(target,actor)} else {sh::advance(lib,programs,source,next,target,actor,rule,owner)}
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn landing_related<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,out:g::Configuration<U,I>,offset:nat,owner:usize,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::well_formed(lib,programs,target),related(eq,a,target,offset,owner),actor!=owner,
        g::step(lib,programs,a,z,actor,rule),g::step(lib,programs,target,out,actor,rule),g::landing(a,z,rule),g::landing(target,out,rule),
        replay::operational_mixed(programs(actor)(a.current[actor].unwrap())),
        g::entry(lib,programs,a,actor).landed.next==g::entry(lib,programs,target,actor).landed.next,
        obs::receipt_related(eq,g::entry(lib,programs,a,actor).landed.receipt,g::entry(lib,programs,target,actor).landed.receipt),
    ensures related(eq,z,out,offset,owner),
{
    ol::frame(eq,lib,programs,a,z,actor,rule);ol::frame(eq,lib,programs,target,out,actor,rule);
    let node=replay::dependent(programs(actor)(a.current[actor].unwrap()));
    sh::source_domains(eq,lib,programs,a,z,actor,rule);sh::source_domains(eq,lib,programs,target,out,actor,rule);
    sh::operation_domains(lib,node,a.state,actor);sh::operation_domains(lib,node,target.state,actor);
    let old=g::entry(lib,programs,a,actor);let new=g::entry(lib,programs,target,actor);histories_push(eq,a.history,target.history,old,new,offset,owner);
    assert forall|n:usize| s::registered(z.state,n) implies {
        &&& z.state.tables[n].dom()==out.state.tables[n].dom()
        &&& (n!=owner ==> z.state.control.fibers[n]==out.state.control.fibers[n] && z.current[n]==out.current[n])
    } by {if n!=actor && n!=owner {assert(a.current[n]==target.current[n]);}}
    assert forall|n:usize| s::registered(z.state,n) && n!=owner implies out.state.accumulators[n]==rename(z.history,offset,owner,z.state.accumulators[n]) by {
        assert(s::registered(a.state,n));
        assert forall|i:int| 0<=i<a.state.accumulators[n].len() implies a.state.accumulators[n][i]<=a.history.len() by {assert(a.state.accumulators[n][i]<a.history.len());}
        if n==actor {
            rename_laws(a.history,offset,owner,a.state.accumulators[n],a.history.len());
            rename_append(a.history,old,offset,owner,a.state.accumulators[n].push(a.history.len()));
        } else {rename_append(a.history,old,offset,owner,a.state.accumulators[n]);}
    }
 }

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn landing_from_call<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,offset:nat,owner:usize,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::well_formed(lib,programs,target),related(eq,a,target,offset,owner),actor!=owner,
        g::step(lib,programs,a,z,actor,rule),g::landing(a,z,rule),replay::operational_mixed(programs(actor)(a.current[actor].unwrap())),
        g::run(lib,programs(actor)(a.current[actor].unwrap()),target.state,actor).is_some(),
        g::entry(lib,programs,a,actor).landed.next==g::entry(lib,programs,target,actor).landed.next,
        obs::receipt_related(eq,g::entry(lib,programs,a,actor).landed.receipt,g::entry(lib,programs,target,actor).landed.receipt),
    ensures {
        let out=advance(lib,programs,a,z,target,actor,rule,owner);
        &&& g::step(lib,programs,target,out,actor,rule) && g::well_formed(lib,programs,out) && related(eq,z,out,offset,owner)
        &&& p::project(out.state,ISet::full())==p::project(g::entry(lib,programs,target,actor).landed.state,ISet::full())
    },
{
    ol::frame(eq,lib,programs,a,z,actor,rule);
    sh::publication(a,target,owner,actor,a.state.control.fibers[actor].committed);
    let out=advance(lib,programs,a,z,target,actor,rule,owner);assert(g::step(lib,programs,target,out,actor,rule));
    ol::configuration_preservation(eq,lib,programs,target,out,actor,rule);ol::frame(eq,lib,programs,target,out,actor,rule);
    landing_related(eq,lib,programs,a,z,target,out,offset,owner,actor,rule);
    let node=replay::dependent(programs(actor)(a.current[actor].unwrap()));
    let landed=dep::run(lib,node,target.state,actor).unwrap().state;lift::run_preservation(dep::stage(lib,node),target.state,actor);p::unique_owner(landed);
    p::lifecycle_edit(landed,actor,z.state.control.fibers[actor].phase,target.state.control.fibers[actor].committed,
        dep::marker(out.current[actor]),target.state.accumulators[actor].push(target.history.len()),ISet::full());
}
pub proof fn foreign_forward<S>(prefix:Seq<fu::Action<S>>,call:fu::Pair<S>,initial:S)
    requires !call.own,sj::foreign(fu::events(prefix),initial).is_some(),
    ensures sj::foreign(fu::events(prefix.push(fu::Action::Forward {call})),initial)==(call.forward)(sj::foreign(fu::events(prefix),initial).unwrap()),
{
    let next=prefix.push(fu::Action::Forward {call});assert(next.drop_last() =~= prefix);assert(fu::events(next).drop_last() =~= fu::events(prefix));
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn landing_transport<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,owner:usize,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),
        fu::fragment(programs,source,labels,source.first().history.len(),owner),g::well_formed(lib,programs,source.last()),g::well_formed(lib,programs,target),
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
    let a=source.last();let offset=source.first().history.len();let id=a.current[actor].unwrap();let node=replay::dependent(programs(actor)(id));
    ol::frame(eq,lib,programs,a,z,actor,rule);ol::run_members(eq,lib,programs,a.state,actor,id);
    assert(programs(actor)(id)==g::Node::Dependent {node});assert(a.state.control.fibers[actor]==target.state.control.fibers[actor]);
    next_call(eq,lib,programs,source,labels,owner,node,target.state,actor);
    landing_from_call(eq,lib,programs,a,z,target,offset,owner,actor,rule);
    let old=g::entry(lib,programs,a,actor);let before=fu::trace_actions(lib,programs,source,labels,offset,owner);let initial=p::project(source.first().state,ISet::full());
    fu::actual_foreign_unload_recovery(eq,lib,programs,source,labels,owner);
    foreign_forward(before,fu::entry_pair(lib,programs,old,owner),initial);
}

pub proof fn own_landing<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,offset:nat,owner:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),related(eq,a,target,offset,owner),g::step(lib,programs,a,z,owner,rule),
        g::landing(a,z,rule),replay::operational_mixed(programs(owner)(a.current[owner].unwrap())),
    ensures related(eq,z,target,offset,owner),
{
    sh::own_landing(eq,lib,programs,a,z,target,owner,rule);ol::frame(eq,lib,programs,a,z,owner,rule);
    let entry=g::entry(lib,programs,a,owner);histories_skip(eq,a.history,target.history,entry,offset,owner);
    assert forall|n:usize| s::registered(z.state,n) && n!=owner implies target.state.accumulators[n]==rename(z.history,offset,owner,z.state.accumulators[n]) by {
        assert(s::registered(a.state,n));assert(z.state.accumulators[n]==a.state.accumulators[n]);
        assert forall|i:int| 0<=i<a.state.accumulators[n].len() implies a.state.accumulators[n][i]<=a.history.len() by {assert(a.state.accumulators[n][i]<a.history.len());}
        rename_append(a.history,entry,offset,owner,a.state.accumulators[n]);
    }
}
pub proof fn control_transport<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,offset:nat,owner:usize,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::well_formed(lib,programs,target),related(eq,a,target,offset,owner),
        g::step(lib,programs,a,z,actor,rule),replay::fragment_step(programs,a,z,actor,rule),!g::landing(a,z,rule),
    ensures {
        let out=advance(lib,programs,a,z,target,actor,rule,owner);
        &&& related(eq,z,out,offset,owner) && g::well_formed(lib,programs,out)
        &&& (sh::keep(actor,rule,owner) ==> g::step(lib,programs,target,out,actor,rule))
        &&& p::project(out.state,ISet::full())==p::project(target.state,ISet::full())
    },
{
    sh::control_step(eq,lib,programs,a,z,target,owner,actor,rule);let out=advance(lib,programs,a,z,target,actor,rule,owner);
    sh::source_domains(eq,lib,programs,a,z,actor,rule);ol::frame(eq,lib,programs,a,z,actor,rule);
    assert forall|n:usize| s::registered(z.state,n) && n!=owner implies out.state.accumulators[n]==rename(z.history,offset,owner,z.state.accumulators[n]) by {
        if n==actor && rule==r::Rule::Begin {rename_laws(a.history,offset,owner,Seq::empty(),0);}
        else {assert(a.state.accumulators[n]==z.state.accumulators[n]);}
    }
}

pub proof fn restore_domains<U,I>(history:Seq<g::Entry<U,I>>,tokens:Seq<nat>,offset:nat,input:s::State<U>,actor:usize)
    requires inv::well_formed(input),fu::tracked_tokens(history,tokens,offset,actor),g::restore(history,tokens,input,actor).is_some(),
        forall|i:int| offset<=i<history.len() ==> simple(#[trigger] history[i].landed.receipt),
    ensures g::restore(history,tokens,input,actor).unwrap().control==input.control,
        forall|n:usize| s::registered(input,n) ==> g::restore(history,tokens,input,actor).unwrap().tables[n].dom()==input.tables[n].dom(),
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let receipt=history[tokens.last() as int].landed.receipt;assert(simple(receipt));
        assert(sh::pinned(receipt,input,actor));fu::table_inverse_projects(receipt,input);
        sh::inverse_definedness(receipt,input,actor);let after=g::undo(receipt,input).unwrap();
        restore_domains(history,tokens.drop_last(),offset,after,actor);
        assert forall|n:usize| s::registered(input,n) implies g::restore(history,tokens,input,actor).unwrap().tables[n].dom()==input.tables[n].dom() by {assert(s::registered(after,n));}
    }
}
pub proof fn no_users<U,I>(source:g::Configuration<U,I>,target:g::Configuration<U,I>,owner:usize,actor:usize)
    requires sh::controls(source,target,owner),!r::relied(source.state.control,actor),
    ensures !r::relied(target.state.control,actor),
{
    if r::relied(target.state.control,actor) {
        let (n,b)=choose|n:usize,b:Binding| s::registered(target.state,n) && n!=actor && target.state.control.fibers[n].phase!=Phase::Inactive
            && target.state.control.fibers[n].committed.contains(b) && b.provider==actor;
        assert(n!=owner);assert(s::registered(source.state,n));assert(source.state.control.fibers[n]==target.state.control.fibers[n]);
        assert(r::relied(source.state.control,actor));
    }
}
pub proof fn append_unload_source<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,z:g::Configuration<U,I>,owner:usize,actor:usize)
    requires g::execution(lib,programs,source,labels),fu::fragment(programs,source,labels,source.first().history.len(),owner),actor!=owner,
        g::step(lib,programs,source.last(),z,actor,r::Rule::Unload),fu::tracked_tokens(source.last().history,source.last().state.accumulators[actor],source.first().history.len(),actor),
    ensures g::execution(lib,programs,source.push(z),labels.push((actor,r::Rule::Unload))),
        fu::fragment(programs,source.push(z),labels.push((actor,r::Rule::Unload)),source.first().history.len(),owner),
{
    assert forall|i:int| 0<=i<labels.push((actor,r::Rule::Unload)).len() implies g::step(lib,programs,source.push(z)[i],source.push(z)[i+1],labels.push((actor,r::Rule::Unload))[i].0,labels.push((actor,r::Rule::Unload))[i].1) by {
        if i<labels.len() {assert(source.push(z)[i]==source[i]);assert(source.push(z)[i+1]==source[i+1]);} else {assert(i==labels.len());}
    }
    assert forall|i:int| 0<=i<labels.push((actor,r::Rule::Unload)).len() && g::landing(source.push(z)[i],source.push(z)[i+1],labels.push((actor,r::Rule::Unload))[i].1)
        implies replay::operational_mixed(programs(labels.push((actor,r::Rule::Unload))[i].0)(source.push(z)[i].current[labels.push((actor,r::Rule::Unload))[i].0].unwrap())) by {
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
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),
        fu::fragment(programs,source,labels,source.first().history.len(),owner),g::well_formed(lib,programs,source.last()),g::well_formed(lib,programs,target),
        related(eq,source.last(),target,source.first().history.len(),owner),actor!=owner,g::step(lib,programs,source.last(),z,actor,r::Rule::Unload),
        fu::tracked_tokens(source.last().history,source.last().state.accumulators[actor],source.first().history.len(),actor),
        pi::context_eq(eq)(sj::foreign(fu::events(fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner)),p::project(source.first().state,ISet::full())).unwrap(),p::project(target.state,ISet::full())),
    ensures {
        let out=g::unload(target,actor);let actions=fu::trace_actions(lib,programs,source.push(z),labels.push((actor,r::Rule::Unload)),source.first().history.len(),owner);let initial=p::project(source.first().state,ISet::full());
        &&& g::step(lib,programs,target,out,actor,r::Rule::Unload) && g::well_formed(lib,programs,out) && related(eq,z,out,source.first().history.len(),owner)
        &&& pi::context_eq(eq)(sj::foreign(fu::events(actions),initial).unwrap(),p::project(out.state,ISet::full()))
    },
{
    let a=source.last();let offset=source.first().history.len();let tokens=a.state.accumulators[actor];let initial=p::project(source.first().state,ISet::full());
    let prefix=fu::trace_actions(lib,programs,source,labels,offset,owner);let reference=sj::foreign(fu::events(prefix),initial).unwrap();
    append_unload_source(lib,programs,source,labels,z,owner,actor);
    fu::actual_source(eq,lib,programs,source,labels,owner);fu::fresh_historical(eq,lib,programs,source,labels);
    fu::actual_foreign_unload_recovery(eq,lib,programs,source,labels,owner);
    fu::actual_foreign_unload_recovery(eq,lib,programs,source.push(z),labels.push((actor,r::Rule::Unload)),owner);
    let actions=fu::trace_actions(lib,programs,source.push(z),labels.push((actor,r::Rule::Unload)),offset,owner);
    assert(source.push(z).drop_last() =~= source);assert(labels.push((actor,r::Rule::Unload)).drop_last() =~= labels);
    assert(actions==prefix+fu::inverse_actions(tokens,offset));
    foreign_inverse_word(lib,programs,a.history,tokens,offset,owner,actor,prefix,initial);
    assert forall|i:int| offset<=i<a.history.len() implies simple(#[trigger] a.history[i].landed.receipt) by {historical_simple(lib,programs,a.history[i]);}
    restore_transport(eq,a.history,target.history,tokens,offset,owner,actor,a.state,target.state,reference);
    restore_domains(a.history,tokens,offset,a.state,actor);
    assert(target.state.accumulators[actor]==rename(a.history,offset,owner,tokens));
    no_users(a,target,owner,actor);let out=g::unload(target,actor);assert(g::step(lib,programs,target,out,actor,r::Rule::Unload));
    ol::configuration_preservation(eq,lib,programs,target,out,actor,r::Rule::Unload);ol::frame(eq,lib,programs,a,z,actor,r::Rule::Unload);ol::frame(eq,lib,programs,target,out,actor,r::Rule::Unload);
    assert forall|n:usize| s::registered(z.state,n) implies {
        &&& z.state.tables[n].dom()==out.state.tables[n].dom()
        &&& (n!=owner ==> z.state.control.fibers[n]==out.state.control.fibers[n] && z.current[n]==out.current[n])
    } by {assert(s::registered(a.state,n));assert(s::registered(target.state,n));}
    assert forall|n:usize| s::registered(z.state,n) && n!=owner implies out.state.accumulators[n]==rename(z.history,offset,owner,z.state.accumulators[n]) by {
        assert(s::registered(a.state,n));if n==actor {rename_laws(a.history,offset,owner,Seq::empty(),0);}
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
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),
        fu::fragment(programs,source,labels,source.first().history.len(),owner),s::registered(source.first().state,owner),
        source.first().state.control.fibers[owner].provisions.is_empty(),source.first().state.control.fibers[owner].phase==Phase::Inactive,
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
    fu::actual_foreign_unload_recovery(eq,lib,programs,source,labels,owner);
    if labels.len()==0 {
        assert(source.len()==1);assert(source.first()==source.last());initial_related(lib,programs,source.first(),owner,eq);
        replay::context_equivalence(eq,lib);assert(pi::context_eq(eq)(initial,initial));
    } else {
        let states=source.drop_last();let previous=labels.drop_last();let label=labels.last();let a=states.last();let z=source.last();let actor=label.0;let rule=label.1;
        assert(g::execution(lib,programs,states,previous));assert(fu::fragment(programs,states,previous,offset,owner));
        delete_execution(eq,lib,programs,states,previous,owner);
        let before=delete(lib,programs,states,previous,owner);let earlier=sh::labels_without(previous,owner);let input=before.last();
        let prefix=fu::trace_actions(lib,programs,states,previous,offset,owner);let out=advance(lib,programs,a,z,input,actor,rule,owner);
        ol::frame(eq,lib,programs,a,z,actor,rule);ol::configuration_preservation(eq,lib,programs,a,z,actor,rule);
        if g::landing(a,z,rule) {
            let entry=g::entry(lib,programs,a,actor);let call=fu::entry_pair(lib,programs,entry,owner);
            assert(actions =~= prefix.push(fu::Action::Forward {call}));assert(actions.drop_last() =~= prefix);assert(fu::events(actions).drop_last() =~= fu::events(prefix));
            if actor==owner {own_landing(eq,lib,programs,a,z,input,offset,owner,rule);assert(call.own);}
            else {landing_transport(eq,lib,programs,states,previous,z,input,owner,actor,rule);}
        } else if rule==r::Rule::Unload {
            assert(actor!=owner);assert(states.push(z) =~= source);assert(previous.push((actor,r::Rule::Unload)) =~= labels);
            unload_transport(eq,lib,programs,states,previous,z,input,owner,actor);
        } else {
            control_transport(eq,lib,programs,a,z,input,offset,owner,actor,rule);
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
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),
        fu::fragment(programs,source,labels,source.first().history.len(),owner),s::registered(source.first().state,owner),source.first().state.control.fibers[owner].provisions.is_empty(),source.first().state.control.fibers[owner].phase==Phase::Inactive,
    ensures forall|i:int| 0<=i<source.len() ==> #[trigger] prefix_valid(eq,lib,programs,source,labels,owner,i),
{
    assert forall|i:int| 0<=i<source.len() implies #[trigger] prefix_valid(eq,lib,programs,source,labels,owner,i) by {
        let states=source.take(i+1);let steps=labels.take(i);
        assert(g::execution(lib,programs,states,steps));assert(fu::fragment(programs,states,steps,source.first().history.len(),owner));
        assert(states.first()==source.first());assert(states.last()==source[i]);delete_execution(eq,lib,programs,states,steps,owner);
    }
}

pub proof fn project_to_tables<U>(eq:spec_fn(Port,U,U)->bool,a:s::State<U>,b:s::State<U>)
    requires inv::well_formed(a),inv::well_formed(b),a.control==b.control,
        forall|n:usize| s::registered(a,n) ==> a.tables[n].dom()==b.tables[n].dom(),pi::context_eq(eq)(p::project(a,ISet::full()),p::project(b,ISet::full())),
    ensures obs::tables_related(eq,a,b),
{
    p::unique_owner(a);p::unique_owner(b);
    assert forall|n:usize| s::registered(a,n) implies {
        &&& a.tables[n].dom()==b.tables[n].dom()
        &&& forall|key:Port| a.tables[n].dom().contains(key) ==> eq(key,a.tables[n][key],b.tables[n][key])
    } by {
        assert forall|key:Port| a.tables[n].dom().contains(key) implies eq(key,a.tables[n][key],b.tables[n][key]) by {
            p::lookup(a,ISet::full(),key,n);p::lookup(b,ISet::full(),key,n);
            assert(crate::observation::context_equal(eq,ISet::full(),p::project(a,ISet::full()),p::project(b,ISet::full())));assert(ISet::<Port>::full().contains(key));
        }
    }
}

/// The closed episode is removed from an actual lifecycle execution. Every
/// provider table has the same final observation, while source and target
/// keep authentic, differently indexed histories and returned inverse maps.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn terminal_deletion<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),
        fu::fragment(programs,source,labels,source.first().history.len(),owner),s::registered(source.first().state,owner),source.first().state.control.fibers[owner].provisions.is_empty(),source.first().state.control.fibers[owner].phase==Phase::Inactive,
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
    delete_execution(eq,lib,programs,source,labels,owner);fu::terminal_with_foreign_unloads(eq,lib,programs,source,labels,owner);
    fu::actual_journal(eq,lib,programs,source,labels,owner);fu::actual_foreign_unload_recovery(eq,lib,programs,source,labels,owner);
    let last=source.last();let terminal=g::unload(last,owner);let target=delete(lib,programs,source,labels,owner);let out=target.last();
    sh::restore_definedness(last.history,last.state.accumulators[owner],last.state,owner);replay::context_equivalence(eq,lib);
    assert(sh::controls(last,out,owner));
    assert forall|n:usize| terminal.state.control.fibers.dom().contains(n) implies #[trigger] terminal.state.control.fibers[n]==out.state.control.fibers[n] by {
        assert(s::registered(last.state,n));
        if n==owner {assert(r::interface_same(last.state.control.fibers[n],out.state.control.fibers[n]));assert(terminal.state.control.fibers[n].committed =~= out.state.control.fibers[n].committed);}
        else {assert(last.state.control.fibers[n]==out.state.control.fibers[n]);}
    }
    assert(terminal.state.control.fibers.dom() =~= last.state.control.fibers.dom());assert(terminal.state.control.fibers.dom()==out.state.control.fibers.dom());
    assert(terminal.state.control.fibers =~= out.state.control.fibers);assert(terminal.state.control==out.state.control);
    assert forall|n:usize| s::registered(terminal.state,n) implies terminal.state.tables[n].dom()==out.state.tables[n].dom() by {
        assert(s::registered(last.state,n));assert(terminal.state.tables[n].dom()==last.state.tables[n].dom());
    }
    let actions=fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner);let initial=p::project(source.first().state,ISet::full());
    assert(pi::context_eq(eq)(p::project(terminal.state,ISet::full()),sj::foreign(fu::events(actions),initial).unwrap()));
    assert(pi::context_eq(eq)(p::project(terminal.state,ISet::full()),p::project(out.state,ISet::full())));
    project_to_tables(eq,terminal.state,out.state);
    reveal(sh::labels_without);assert(labels.push((owner,r::Rule::Unload)).drop_last() =~= labels);
    assert(g::execution(lib,programs,source.push(terminal),labels.push((owner,r::Rule::Unload)))) by {
        assert forall|i:int| 0<=i<labels.push((owner,r::Rule::Unload)).len() implies g::step(lib,programs,source.push(terminal)[i],source.push(terminal)[i+1],labels.push((owner,r::Rule::Unload))[i].0,labels.push((owner,r::Rule::Unload))[i].1) by {
            if i<labels.len() {assert(source.push(terminal)[i+1]==source[i+1]);} else {assert(i==labels.len());}
        }
    }
}

/// A real +5 owner / +7 foreign execution with a nonempty provider history.
/// The source foreign inverse lives at token 2; its target counterpart lives
/// at token 1 and is used by an actual target lifecycle Unload.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn actual_compressed_unload()
    ensures {
        let source=fu::mixed_trace();let labels=fu::mixed_labels();let target=delete(ex::library(),sh::example_programs(),source,labels,1);
        let terminal=g::unload(source.last(),1);let before=target[target.len() as int-2];
        &&& g::execution(ex::library(),sh::example_programs(),target,sh::labels_without(labels,1))
        &&& g::step(ex::library(),sh::example_programs(),source.last(),terminal,1,r::Rule::Unload)
        &&& g::step(ex::library(),sh::example_programs(),before,target.last(),2,r::Rule::Unload)
        &&& target.len()==7 && target.first().history.len()==1 && target.last().history.len()==2
        &&& target.last().history[0]==source.first().history[0]
        &&& source[source.len() as int-2].state.accumulators[2usize]==seq![2nat]
        &&& before.state.accumulators[2usize]==seq![1nat]
        &&& target.last().state.accumulators[2usize].len()==0
        &&& obs::receipt_related(ex::equality(),source.last().history[2].landed.receipt,target.last().history[1].landed.receipt)
        &&& obs::tables_related(ex::equality(),terminal.state,target.last().state)
        &&& g::well_formed(ex::library(),sh::example_programs(),target.last())
    },
{
    fu::mixed_execution();sh::example_interface();let lib=ex::library();let programs=sh::example_programs();let source=fu::mixed_trace();let labels=fu::mixed_labels();
    terminal_deletion(ex::equality(),lib,programs,source,labels,1);delete_execution(ex::equality(),lib,programs,source,labels,1);
    reveal(fu::mixed_trace);reveal(sh::example_trace);reveal_with_fuel(sh::labels_without,10);reveal_with_fuel(index,4);
    let target=delete(lib,programs,source,labels,1);let prefix=source.drop_last();let earlier=labels.drop_last();
    assert(prefix.len()==9);assert(labels.len()==9);assert(source.len()==10);
    assert(g::execution(lib,programs,prefix,earlier));assert(fu::fragment(programs,prefix,earlier,1,1));
    assert(prefix.first()==source.first());delete_execution(ex::equality(),lib,programs,prefix,earlier,1);
    let previous=delete(lib,programs,prefix,earlier,1);let a=prefix.last();let b=previous.last();
    assert(a.state.accumulators[2usize] =~= seq![2nat]);
    assert(g::owner(a.history[1].landed.receipt)==1);assert(g::owner(a.history[2].landed.receipt)==2);
    assert(index(a.history,1,1,2)==1);assert(index(a.history,1,1,3)==2);
    assert(b.state.accumulators[2usize] =~= seq![1nat]);
    reveal(delete);assert(target==previous.push(advance(lib,programs,a,source.last(),b,2,r::Rule::Unload,1)));
    assert(target[target.len() as int-2]==b);
    assert(sh::labels_without(labels,1).last()==(2usize,r::Rule::Unload));
    assert(source.last().history==a.history);
    assert(target.last().history==b.history);
}

} // verus!
