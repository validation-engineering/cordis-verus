//! Strict inverse-journal recovery across external orchestration.
//!
//! Reverse restoration is derived from each actually successful captured
//! inverse. Remove cannot cross an Unload that still retains its child receipt.
#[cfg(verus_keep_ghost)]
use crate::{
    administrative_orchestration as admin, child_history as ch, dependent_lift as dep, global,
    grammar_lift as lift, mixed_grammar as g, mixed_orchestration as o, mixed_transposition as t,
    observational_grammar as og, observational_lift as ol, preservation as inv, refinement as r,
    semantics as s, Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn change<U>(a:s::State<U>,id:usize,rule:r::Rule,parent:Option<usize>,dependencies:ISet<Port>,provisions:ISet<Port>)->s::State<U> {
    match rule {
        r::Rule::Insert=>s::extend_child(a,global::insert_fiber(a.control,id,parent,dependencies,provisions),id,0),
        r::Rule::Retire=>s::with_control(a,global::retire_fiber(a.control,id)),
        _=>s::erase(a,id),
    }
}
pub open spec fn avoids<U>(receipt:g::Receipt<U>,id:usize)->bool {
    g::owner(receipt)!=id && match receipt {
        g::Receipt::Table {receipt}=>match receipt.inverse {lift::Inverse::Operation {provider,..}=>provider!=id,_=>true},
        g::Receipt::Child {child,..}=>child!=id,
    }
}
pub open spec fn no_child<U,I>(history:Seq<g::Entry<U,I>>,tokens:Seq<nat>,id:usize)->bool {
    forall|token:nat| tokens.contains(token) ==> #[trigger] g::kind(history)(token)!=Some(id)
}
pub open spec fn crossing_guard<U,I>(a:g::Configuration<U,I>,actor:usize,id:usize,external:r::Rule)->bool {
    external==r::Rule::Insert || external==r::Rule::Retire
        || external==r::Rule::Remove && id!=actor && no_child(a.history,a.state.accumulators[actor],id)
}

/// A primitive inverse reads only its recorded actor/provider/child and the
/// relevant scalar slot. Retired flags do not participate in resolution.
pub proof fn undo_cross<U>(receipt:g::Receipt<U>,a:s::State<U>,id:usize,rule:r::Rule,
    parent:Option<usize>,dependencies:ISet<Port>,provisions:ISet<Port>)
    requires g::undo(receipt,a).is_some(),
        rule==r::Rule::Insert && !s::registered(a,id)
        || rule==r::Rule::Retire && s::registered(a,id)
        || rule==r::Rule::Remove && s::registered(a,id) && avoids(receipt,id),
    ensures {
        let old=g::undo(receipt,a).unwrap();let input=change(a,id,rule,parent,dependencies,provisions);
        &&& g::undo(receipt,input)==Some(change(old,id,rule,parent,dependencies,provisions))
        &&& (rule==r::Rule::Remove ==> old.control.fibers[id]==a.control.fibers[id] && old.tables[id]==a.tables[id])
    },
{
    let input=change(a,id,rule,parent,dependencies,provisions);
    match receipt {
        g::Receipt::Table {receipt}=>{
            assert(s::registered(a,receipt.actor));
            if rule!=r::Rule::Retire {assert(receipt.actor!=id);}
            match receipt.inverse {
                lift::Inverse::Operation {provider,key,..}=>{
                    assert(s::registered(a,provider));
                    if rule!=r::Rule::Retire {assert(provider!=id);}
                    assert(lift::resolve(a,receipt.actor,key)==lift::resolve(input,receipt.actor,key));
                    assert(input.tables[provider]==a.tables[provider]);
                },
                _=>{},
            }
        },
        g::Receipt::Child {child,..}=>{
            assert(s::registered(a,child));if rule!=r::Rule::Retire {assert(child!=id);}
        },
    }
    assert(g::undo(receipt,input).is_some());
    let actual=g::undo(receipt,input).unwrap();let expected=change(g::undo(receipt,a).unwrap(),id,rule,parent,dependencies,provisions);
    assert(actual.control.fibers =~= expected.control.fibers);
    assert(actual.tables =~= expected.tables);
    assert(actual.effects =~= expected.effects);assert(actual.iterators =~= expected.iterators);assert(actual.accumulators =~= expected.accumulators);
}

/// A successful operation inverse cannot resolve an Inactive foreign provider.
/// This is derived from installed commitments, not from a supplied read set.
pub proof fn inactive_avoided<U>(receipt:g::Receipt<U>,a:s::State<U>,id:usize)
    requires inv::well_formed(a),g::undo(receipt,a).is_some(),s::registered(a,id),a.control.fibers[id].phase==Phase::Inactive,
        g::owner(receipt)!=id,g::captured_child(receipt)!=Some(id),
    ensures avoids(receipt,id),
{
    if let g::Receipt::Table {receipt}=receipt {
        if let lift::Inverse::Operation {provider,key,..}=receipt.inverse {
            lift::resolution_sound(a,receipt.actor,key);
            if provider!=receipt.actor {
                assert(a.control.fibers[receipt.actor].committed.contains(Binding {key:key.key,realm:key.realm,provider}));
                assert(a.control.fibers[provider].phase!=Phase::Inactive);
            }
        }
    }
}

/// Actual source success is sufficient: no domain or result of the reverse
/// restore is an input. Scalar inverse domains remain checked by the interpreter.
pub proof fn restore_cross<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,history:Seq<g::Entry<U,I>>,tokens:Seq<nat>,
    a:s::State<U>,actor:usize,id:usize,rule:r::Rule,parent:Option<usize>,dependencies:ISet<Port>,provisions:ISet<Port>)
    requires inv::well_formed(a),dep::typed(lib,a),dep::finite_context(a),g::history_sound(lib,programs,history),g::restore(history,tokens,a,actor).is_some(),
        rule==r::Rule::Insert && !s::registered(a,id)
        || rule==r::Rule::Retire && s::registered(a,id)
        || rule==r::Rule::Remove && s::registered(a,id) && a.control.fibers[id].phase==Phase::Inactive && id!=actor && no_child(history,tokens,id),
    ensures {
        let old=g::restore(history,tokens,a,actor).unwrap();let input=change(a,id,rule,parent,dependencies,provisions);
        &&& g::restore(history,tokens,input,actor)==Some(change(old,id,rule,parent,dependencies,provisions))
        &&& (rule==r::Rule::Remove ==> old.control.fibers[id]==a.control.fibers[id] && old.tables[id]==a.tables[id])
    },
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let token=tokens.last();let receipt=history[token as int].landed.receipt;
        assert(g::owner(receipt)==actor);assert(g::undo(receipt,a).is_some());
        if rule==r::Rule::Remove {
            assert(tokens.contains(token));assert(g::kind(history)(token)!=Some(id));assert(g::captured_child(receipt)!=Some(id));inactive_avoided(receipt,a,id);
            assert(no_child(history,tokens.drop_last(),id)) by {
                assert forall|t:nat| tokens.drop_last().contains(t) implies #[trigger] g::kind(history)(t)!=Some(id) by {assert(tokens.contains(t));}
            }
        }
        undo_cross(receipt,a,id,rule,parent,dependencies,provisions);
        g::inverse_preservation(lib,receipt,a);
        let next=g::undo(receipt,a).unwrap();
        restore_cross(lib,programs,history,tokens.drop_last(),next,actor,id,rule,parent,dependencies,provisions);
    }
}

pub open spec fn reverse<U,I>(a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,id:usize,external:r::Rule)->g::Configuration<U,I> {
    g::unload(o::intermediate(a,z,id,external),actor)
}

/// Exchange Unload with an actual external action, preserving the complete
/// endpoint. Remove alone needs the captured-child guard and another actor.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn diamond<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,b:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,id:usize,external:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,b,actor,r::Rule::Unload),
        g::step(lib,programs,b,z,id,external),crossing_guard(a,actor,id,external),
    ensures {
        let middle=o::intermediate(a,z,id,external);let last=reverse(a,z,actor,id,external);
        &&& g::step(lib,programs,a,middle,id,external) && g::step(lib,programs,middle,last,actor,r::Rule::Unload)
        &&& last==z && last.history==a.history
        &&& g::well_formed(lib,programs,middle) && g::well_formed(lib,programs,last)
    },
{
    let recovered=g::restore(a.history,a.state.accumulators[actor],a.state,actor).unwrap();
    g::restore_preservation(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);
    admin::external_form(lib,programs,b,z,id,external);
    let middle=o::intermediate(a,z,id,external);let last=reverse(a,z,actor,id,external);
    let f=if external==r::Rule::Insert {z.state.control.fibers[id]} else {a.state.control.fibers[actor]};
    assert(b.state.control.fibers.dom() =~= a.state.control.fibers.dom());
    assert forall|n:usize| s::registered(a.state,n) implies r::interface_same(a.state.control.fibers[n],b.state.control.fibers[n])
        && (n!=actor ==> a.state.control.fibers[n].phase==b.state.control.fibers[n].phase) by {}
    match external {
        r::Rule::Insert=>{
            o::insertion_form(lib,programs,b,z,id);assert(!s::registered(a.state,id));assert(id!=actor);
            assert forall|n:usize,k:Port| s::registered(a.state,n) && a.state.control.fibers[n].provisions.contains(k)
                implies !f.provisions.contains(k) by {assert(s::registered(b.state,n));assert(b.state.control.fibers[n].provisions.contains(k));}
            assert(t::insertion_ready(lib,programs,a,id,f.parent,f.dependencies,f.provisions,z.roots[id]));
            t::insertion_step(lib,programs,a,id,f.parent,f.dependencies,f.provisions,z.roots[id]);
        },
        r::Rule::Retire=>{
            assert(s::registered(a.state,id));ch::concrete_child_retirement(a.state,id);
            assert(g::step(lib,programs,a,middle,id,r::Rule::Retire));
        },
        r::Rule::Remove=>{
            assert(r::step(b.state.control,z.state.control,id,r::Rule::Remove));assert(s::registered(a.state,id));
            assert(a.state.control.fibers[id].phase==Phase::Inactive);
        },
        _=>{},
    }
    restore_cross(lib,programs,a.history,a.state.accumulators[actor],a.state,actor,id,external,f.parent,f.dependencies,f.provisions);
    if external==r::Rule::Remove {
        assert(recovered.control.fibers[id]==a.state.control.fibers[id]);assert(recovered.tables[id]==a.state.tables[id]);
        assert(b.state.control.fibers[id]==a.state.control.fibers[id]);
        assert(r::frame(a.state.control,middle.state.control,id));
        assert forall|n:usize| r::registered(a.state.control,n) implies a.state.control.fibers[n].parent!=Some(id) by {assert(s::registered(a.state,n));assert(s::registered(b.state,n));
            assert(r::interface_same(a.state.control.fibers[n],recovered.control.fibers[n]));
            assert(b.state.control.fibers[n].parent==recovered.control.fibers[n].parent);
            assert(b.state.control.fibers[n].parent!=Some(id));}
        assert(r::step(b.state.control,z.state.control,id,r::Rule::Remove));
        assert(a.state.control.fibers[id].retired);assert(a.state.control.fibers[id].committed.is_empty());
        assert(!s::registered(middle.state,id));
        assert(s::registered(a.state,id));assert(a.state.control.fibers[id].phase==Phase::Inactive);
        assert(r::frame(a.state.control,middle.state.control,id));
        assert(r::step(a.state.control,middle.state.control,id,r::Rule::Remove));
        assert(ch::remove_unreferenced(g::kind(a.history),a.state,id)) by {
            assert forall|n:usize,token:nat| s::registered(a.state,n) && #[trigger] a.state.accumulators[n].contains(token)
                implies g::kind(a.history)(token)!=Some(id) by {
                if n==actor {assert(no_child(a.history,a.state.accumulators[actor],id));}
                else {assert(s::registered(b.state,n));assert(b.state.accumulators[n].contains(token));}
            }
        }
        assert(g::step(lib,programs,a,middle,id,r::Rule::Remove));
    }
    assert(middle.state==change(a.state,id,external,f.parent,f.dependencies,f.provisions));
    assert(middle.state.accumulators[actor]==a.state.accumulators[actor]);
    assert(!r::relied(middle.state.control,actor)) by {
        assert forall|n:usize,binding:Binding| s::registered(middle.state,n) && n!=actor && middle.state.control.fibers[n].phase!=Phase::Inactive
            && middle.state.control.fibers[n].committed.contains(binding) implies binding.provider!=actor by {
            assert(s::registered(a.state,n));
        }
    }
    assert(g::step(lib,programs,middle,last,actor,r::Rule::Unload));
    assert(z.state.control.fibers =~= last.state.control.fibers);
    assert(z.state.tables =~= last.state.tables);assert(z.state.effects =~= last.state.effects);
    assert(z.state.iterators =~= last.state.iterators);assert(z.state.accumulators =~= last.state.accumulators);assert(z.current =~= last.current);
    ol::configuration_preservation(eq,lib,programs,a,middle,id,external);
    ol::configuration_preservation(eq,lib,programs,middle,last,actor,r::Rule::Unload);
}

/// Since histories and the whole endpoint coincide, every supplied legal
/// suffix remains the same actual execution after the constructed crossing.
pub proof fn suffix<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,b:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,id:usize,external:r::Rule,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,b,actor,r::Rule::Unload),
        g::step(lib,programs,b,z,id,external),crossing_guard(a,actor,id,external),g::execution(lib,programs,source,labels),source.first()==z,
    ensures {
        let middle=o::intermediate(a,z,id,external);let result=seq![a,middle]+source;let reordered=seq![(id,external),(actor,r::Rule::Unload)]+labels;
        &&& g::execution(lib,programs,result,reordered) && result.first()==a && result.last()==source.last()
        &&& forall|i:int| 0<=i<result.len() ==> g::well_formed(lib,programs,result[i])
    },
{
    diamond(eq,lib,programs,a,b,z,actor,id,external);
    let middle=o::intermediate(a,z,id,external);let result=seq![a,middle]+source;let reordered=seq![(id,external),(actor,r::Rule::Unload)]+labels;
    assert(g::execution(lib,programs,result,reordered)) by {
        assert forall|i:int| 0<=i<reordered.len() implies g::step(lib,programs,result[i],result[i+1],reordered[i].0,reordered[i].1) by {
            if i==0 {assert(result[i]==a);assert(result[i+1]==middle);}
            else if i==1 {assert(result[i]==middle);assert(result[i+1]==z);}
            else {assert(result[i]==source[i-2]);assert(result[i+1]==source[i-1]);assert(reordered[i]==labels[i-2]);
                assert(g::step(lib,programs,source[i-2],source[i-1],labels[i-2].0,labels[i-2].1));}
        }
    }
    ol::execution_preservation(eq,lib,programs,result,reordered);
}

/// The real +5 inverse and provision inverse run before retirement of the
/// captured child. Moving that retirement first preserves every scalar result.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn actual_operation_retire()
    ensures {
        let a=crate::recovery_examples::trace()[10];let b=crate::recovery_examples::trace()[11];let z=o::retire(b,1);
        let lib=crate::recovery_examples::library();let programs=crate::recovery_examples::programs();
        &&& a.state.tables[0usize][crate::recovery_examples::key(0)]==12
        &&& g::step(lib,programs,a,b,0,r::Rule::Unload) && g::step(lib,programs,b,z,1,r::Rule::Retire)
        &&& g::step(lib,programs,a,o::retire(a,1),1,r::Rule::Retire) && g::step(lib,programs,o::retire(a,1),z,0,r::Rule::Unload)
        &&& z.state.tables[0usize].is_empty() && z.state.tables[1usize][crate::recovery_examples::key(1)]==39
        &&& z.state.control.fibers[1usize].retired && z.state.control.fibers[1usize].phase==Phase::Active
        &&& z.history==a.history
    },
{
    crate::recovery_examples::actual_execution();crate::recovery_examples::primitive_theory();
    let eq=crate::recovery_examples::equality();let lib=crate::recovery_examples::library();let programs=crate::recovery_examples::programs();
    og::exact_theory(eq,lib);ol::from_empty_safe(eq,lib,programs,crate::recovery_examples::trace(),crate::recovery_examples::labels());
    reveal(crate::recovery_examples::trace);reveal_with_fuel(g::restore,4);
    let a=crate::recovery_examples::trace()[10];let b=crate::recovery_examples::trace()[11];let z=o::retire(b,1);
    ch::concrete_child_retirement(b.state,1);assert(g::step(lib,programs,b,z,1,r::Rule::Retire));
    diamond(eq,lib,programs,a,b,z,0,1,r::Rule::Retire);
}

pub open spec fn retained_source()->g::Configuration<u64,bool> {
    let source=o::retire(o::retire(crate::mixed_examples::trace()[3],1),0);
    g::edit(source,0,Phase::Unloading,ISet::empty(),None,source.state.accumulators[0usize])
}
/// Even already retired, Inactive, empty children remain live inverse targets.
/// The original Unload then Remove is legal; moving Remove first is not.
pub proof fn retained_remove_blocks()
    ensures {
        let a=retained_source();let b=g::unload(a,0);let z=o::remove(b,1);
        let lib=crate::mixed_examples::library();let programs=crate::mixed_examples::programs();
        &&& g::well_formed(lib,programs,a)
        &&& g::step(lib,programs,a,b,0,r::Rule::Unload) && g::step(lib,programs,b,z,1,r::Rule::Remove)
        &&& a.state.control.fibers[1usize].retired && a.state.control.fibers[1usize].phase==Phase::Inactive
        &&& r::step(a.state.control,o::remove(a,1).state.control,1,r::Rule::Remove)
        &&& !g::step(lib,programs,a,o::remove(a,1),1,r::Rule::Remove)
        &&& !crossing_guard(a,0,1,r::Rule::Remove)
        &&& g::restore(a.history,a.state.accumulators[0usize],o::remove(a,1).state,0).is_none()
    },
{
    crate::mixed_examples::actual_execution();crate::mixed_examples::primitive_theory();
    let eq=crate::mixed_examples::equality();let lib=crate::mixed_examples::library();let programs=crate::mixed_examples::programs();
    og::exact_theory(eq,lib);ol::from_empty_safe(eq,lib,programs,crate::mixed_examples::trace(),crate::mixed_examples::labels());
    reveal(crate::mixed_examples::trace);
    let source=crate::mixed_examples::trace()[3];let child_retired=o::retire(source,1);let parent_retired=o::retire(child_retired,0);
    ch::concrete_child_retirement(source.state,1);assert(g::step(lib,programs,source,child_retired,1,r::Rule::Retire));
    ol::configuration_preservation(eq,lib,programs,source,child_retired,1,r::Rule::Retire);
    ch::concrete_child_retirement(child_retired.state,0);assert(g::step(lib,programs,child_retired,parent_retired,0,r::Rule::Retire));
    ol::configuration_preservation(eq,lib,programs,child_retired,parent_retired,0,r::Rule::Retire);
    let a=retained_source();let b=g::unload(a,0);let z=o::remove(b,1);
    assert(g::step(lib,programs,parent_retired,a,0,r::Rule::Divert));
    ol::configuration_preservation(eq,lib,programs,parent_retired,a,0,r::Rule::Divert);
    assert(a.state.accumulators[0usize] =~= seq![0nat]);reveal_with_fuel(g::restore,2);
    assert(g::step(lib,programs,a,b,0,r::Rule::Unload));
    assert forall|n:usize| s::registered(a.state,n) implies a.state.control.fibers[n].parent!=Some(1usize) by {assert(n==0 || n==1);}
    assert forall|n:usize| s::registered(b.state,n) implies b.state.accumulators[n].len()==0 by {assert(n==0 || n==1);}
    assert(ch::remove_unreferenced(g::kind(b.history),b.state,1));
    assert(g::kind(a.history)(0nat)==Some(1usize));assert(a.state.accumulators[0usize].contains(0nat));
}

/// The same nonempty inverse journal crosses fresh insertion and later removal
/// of an unrelated empty entry; no reverse execution is supplied by a caller.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn actual_operation_insert_remove()
    ensures {
        let a=crate::recovery_examples::trace()[10];let b=crate::recovery_examples::trace()[11];
        let root=crate::recovery_examples::Stage::Spawn;
        let middle=t::insert(a,2,None,ISet::empty(),ISet::empty(),root);let z=t::insert(b,2,None,ISet::empty(),ISet::empty(),root);
        let retired=o::retire(middle,2);let cleaned=o::retire(z,2);
        let lib=crate::recovery_examples::library();let programs=crate::recovery_examples::programs();
        &&& g::step(lib,programs,a,middle,2,r::Rule::Insert) && g::step(lib,programs,middle,z,0,r::Rule::Unload)
        &&& g::step(lib,programs,retired,cleaned,0,r::Rule::Unload) && g::step(lib,programs,cleaned,b,2,r::Rule::Remove)
        &&& g::step(lib,programs,retired,a,2,r::Rule::Remove) && g::step(lib,programs,a,b,0,r::Rule::Unload)
        &&& a.state.tables[0usize][crate::recovery_examples::key(0)]==12 && b.state.tables[0usize].is_empty()
    },
{
    crate::recovery_examples::actual_execution();crate::recovery_examples::primitive_theory();
    let eq=crate::recovery_examples::equality();let lib=crate::recovery_examples::library();let programs=crate::recovery_examples::programs();
    og::exact_theory(eq,lib);ol::from_empty_safe(eq,lib,programs,crate::recovery_examples::trace(),crate::recovery_examples::labels());
    reveal(crate::recovery_examples::trace);reveal_with_fuel(g::restore,4);
    let a=crate::recovery_examples::trace()[10];let b=crate::recovery_examples::trace()[11];let root=crate::recovery_examples::Stage::Spawn;
    crate::mixed_syntax::constructor_member(lib,programs,2,ISet::empty(),ISet::empty(),root);
    assert(ISet::<Port>::empty().union(ISet::empty()) =~= ISet::<Port>::empty());
    t::insertion_step(lib,programs,b,2,None,ISet::empty(),ISet::empty(),root);
    let middle=t::insert(a,2,None,ISet::empty(),ISet::empty(),root);let z=t::insert(b,2,None,ISet::empty(),ISet::empty(),root);
    diamond(eq,lib,programs,a,b,z,0,2,r::Rule::Insert);
    let retired=o::retire(middle,2);let cleaned=o::retire(z,2);
    ch::concrete_child_retirement(z.state,2);assert(g::step(lib,programs,z,cleaned,2,r::Rule::Retire));
    diamond(eq,lib,programs,middle,z,cleaned,0,2,r::Rule::Retire);
    assert(o::remove(retired,2).state.control.fibers =~= a.state.control.fibers);
    assert(o::remove(retired,2).state.tables =~= a.state.tables);assert(o::remove(retired,2).state.effects =~= a.state.effects);
    assert(o::remove(retired,2).state.iterators =~= a.state.iterators);assert(o::remove(retired,2).state.accumulators =~= a.state.accumulators);
    assert(o::remove(retired,2).roots =~= a.roots);assert(o::remove(retired,2).current =~= a.current);
    assert(o::remove(cleaned,2).state.control.fibers =~= b.state.control.fibers);
    assert(o::remove(cleaned,2).state.tables =~= b.state.tables);assert(o::remove(cleaned,2).state.effects =~= b.state.effects);
    assert(o::remove(cleaned,2).state.iterators =~= b.state.iterators);assert(o::remove(cleaned,2).state.accumulators =~= b.state.accumulators);
    assert(o::remove(cleaned,2).roots =~= b.roots);assert(o::remove(cleaned,2).current =~= b.current);
    assert forall|n:usize| s::registered(cleaned.state,n) implies cleaned.state.control.fibers[n].parent!=Some(2usize) by {assert(n==0 || n==1 || n==2);}
    assert forall|n:usize,token:nat| s::registered(cleaned.state,n) && #[trigger] cleaned.state.accumulators[n].contains(token)
        implies g::kind(cleaned.history)(token)!=Some(2usize) by {
        assert(n==1);assert(token==1 || token==2);assert(g::kind(cleaned.history)(token)==None);
    }
    assert(g::step(lib,programs,cleaned,b,2,r::Rule::Remove));
    assert forall|token:nat| retired.state.accumulators[0usize].contains(token) implies #[trigger] g::kind(retired.history)(token)!=Some(2usize) by {
        assert(token==0 || token==3 || token==4);
    }
    diamond(eq,lib,programs,retired,cleaned,b,0,2,r::Rule::Remove);
}

} // verus!
