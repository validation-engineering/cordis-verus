//! Operation inverse domains reconstructed from actual source histories.
//!
//! Live journals retain their episode's committed provider. Its registry entry
//! and value slot survive foreign transitions: a dependency prevents provider
//! unload, and a journal's own unload clears that journal. Forward Provision
//! cannot alias an earlier operation on the owner's table because the slot is
//! already present. This proves domains, not arbitrary scalar inverse totality.
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_grammar as d, fresh_grammar as fg, fresh_semantics as fs, grammar_lift as gl,
    mixed_grammar as mx, mixed_recovery as mr, preservation as inv, provision_history as ph,
    refinement as r, semantics as s, Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn operation_slot<U>(receipt:mx::Receipt<U>)->Option<(usize,Port)> {
    match receipt {
        mx::Receipt::Table {receipt}=>match receipt.inverse {
            gl::Inverse::Operation {provider,key,..}=>Some((provider,key)),_=>None,
        },
        _=>None,
    }
}

pub open spec fn operation_at<U,I>(a:mx::Configuration<U,I>,actor:usize,i:int)->Option<(usize,Port)> {
    operation_slot(a.history[a.state.accumulators[actor][i] as int].landed.receipt)
}

/// Captured identity, current slot presence, and LIFO Provision separation are
/// properties of the actual retained accumulator, including failed prefixes.
pub open spec fn live_operations<U,I>(a:mx::Configuration<U,I>)->bool {
    &&& forall|n:usize,i:int| s::registered(a.state,n) && 0<=i<a.state.accumulators[n].len()
        && #[trigger] operation_at(a,n,i).is_some()
        ==> gl::resolve(a.state,n,operation_at(a,n,i).unwrap().1)==Some(operation_at(a,n,i).unwrap().0)
    &&& forall|n:usize,i:int| s::registered(a.state,n) && 0<=i<a.state.accumulators[n].len()
        && #[trigger] operation_at(a,n,i).is_some() ==> {
            let slot=operation_at(a,n,i).unwrap();
            &&& s::registered(a.state,slot.0)
            &&& a.state.tables[slot.0].dom().contains(slot.1)
        }
    &&& forall|n:usize,i:int,j:int| s::registered(a.state,n) && 0<=i<j<a.state.accumulators[n].len()
        && #[trigger] operation_at(a,n,i).is_some() && #[trigger] ph::provision_at(a,n,j).is_some()
        ==> operation_at(a,n,i).unwrap().0!=n || operation_at(a,n,i).unwrap().1!=ph::provision_at(a,n,j).unwrap()
}

spec fn stable_resolution<U>(a:s::State<U>,z:s::State<U>,n:usize)->bool {
    &&& s::registered(a,n) && s::registered(z,n)
    &&& a.control.fibers[n].dependencies==z.control.fibers[n].dependencies
    &&& a.control.fibers[n].provisions==z.control.fibers[n].provisions
    &&& a.control.fibers[n].committed==z.control.fibers[n].committed
}

proof fn same_resolution<U>(a:s::State<U>,z:s::State<U>,n:usize,key:Port)
    requires stable_resolution(a,z,n),
    ensures gl::resolve(a,n,key)==gl::resolve(z,n,key),
{}

/// A common projection of the actual Mixed/Fresh rule. The premise records
/// local control and table frames, not the successor's live-journal invariant.
spec fn journal_step<U,I>(a:mx::Configuration<U,I>,z:mx::Configuration<U,I>)->bool {
    &&& a.history.len()<=z.history.len()
    &&& forall|i:int| 0<=i<a.history.len() ==> #[trigger] a.history[i]==z.history[i]
    &&& forall|n:usize| s::registered(z.state,n) && z.state.accumulators[n].len()>0 ==> {
        &&& stable_resolution(a.state,z.state,n)
        &&& forall|key:Port| gl::resolve(a.state,n,key).is_some()
            && a.state.tables[gl::resolve(a.state,n,key).unwrap()].dom().contains(key) ==> {
                let provider=gl::resolve(a.state,n,key).unwrap();
                &&& s::registered(z.state,provider)
                &&& z.state.tables[provider].dom().contains(key)
            }
        &&& (z.state.accumulators[n]==a.state.accumulators[n]
            || (z.state.accumulators[n]==a.state.accumulators[n].push(a.history.len())
                && z.history.len()==a.history.len()+1
                && (operation_slot(z.history.last().landed.receipt).is_some() ==> {
                    let slot=operation_slot(z.history.last().landed.receipt).unwrap();
                    &&& gl::resolve(z.state,n,slot.1)==Some(slot.0)
                    &&& s::registered(z.state,slot.0)
                    &&& z.state.tables[slot.0].dom().contains(slot.1)
                })
                && (ph::provision_key(z.history.last().landed.receipt).is_some()
                    ==> !a.state.tables[n].dom().contains(ph::provision_key(z.history.last().landed.receipt).unwrap()))))
    }
}

proof fn old_slot<U,I>(a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,n:usize,i:int)
    requires mx::tokens_valid(a),journal_step(a,z),s::registered(z.state,n),
        0<=i<a.state.accumulators[n].len(),i<z.state.accumulators[n].len(),
    ensures operation_at(a,n,i)==operation_at(z,n,i),ph::provision_at(a,n,i)==ph::provision_at(z,n,i),
{
    let token=a.state.accumulators[n][i];
    assert(token<a.history.len());
    assert(z.state.accumulators[n][i]==token);
    assert(a.history[token as int]==z.history[token as int]);
}

proof fn journal_preservation<U,I>(a:mx::Configuration<U,I>,z:mx::Configuration<U,I>)
    requires mx::tokens_valid(a),live_operations(a),journal_step(a,z),
    ensures live_operations(z),
{
    assert forall|n:usize,i:int| s::registered(z.state,n) && 0<=i<z.state.accumulators[n].len()
        && #[trigger] operation_at(z,n,i).is_some()
        implies gl::resolve(z.state,n,operation_at(z,n,i).unwrap().1)==Some(operation_at(z,n,i).unwrap().0) by {
        if i<a.state.accumulators[n].len() {
            old_slot(a,z,n,i);
            let slot=operation_at(a,n,i).unwrap();
            same_resolution(a.state,z.state,n,slot.1);
        } else {
            assert(i==a.state.accumulators[n].len());
            assert(z.state.accumulators[n][i]==a.history.len());
            assert(z.history[a.history.len() as int]==z.history.last());
        }
    }
    assert forall|n:usize,i:int| s::registered(z.state,n) && 0<=i<z.state.accumulators[n].len()
        && #[trigger] operation_at(z,n,i).is_some() implies {
            let slot=operation_at(z,n,i).unwrap();
            &&& s::registered(z.state,slot.0)
            &&& z.state.tables[slot.0].dom().contains(slot.1)
        } by {
        if i<a.state.accumulators[n].len() {
            old_slot(a,z,n,i);
            let slot=operation_at(a,n,i).unwrap();
            assert(gl::resolve(a.state,n,slot.1)==Some(slot.0));
        } else {
            assert(i==a.state.accumulators[n].len());
            assert(z.state.accumulators[n][i]==a.history.len());
            assert(z.history[a.history.len() as int]==z.history.last());
        }
    }
    assert forall|n:usize,i:int,j:int| s::registered(z.state,n) && 0<=i<j<z.state.accumulators[n].len()
        && #[trigger] operation_at(z,n,i).is_some() && #[trigger] ph::provision_at(z,n,j).is_some()
        implies operation_at(z,n,i).unwrap().0!=n || operation_at(z,n,i).unwrap().1!=ph::provision_at(z,n,j).unwrap() by {
        assert(i<a.state.accumulators[n].len());
        old_slot(a,z,n,i);
        if j<a.state.accumulators[n].len() {
            old_slot(a,z,n,j);
        } else {
            assert(j==a.state.accumulators[n].len());
            assert(z.state.accumulators[n][j]==a.history.len());
            assert(z.history[a.history.len() as int]==z.history.last());
            let slot=operation_at(a,n,i).unwrap();
            assert(a.state.tables[slot.0].dom().contains(slot.1));
        }
    }
}

proof fn run_domains<A,X,U,B,I>(lib:mx::Library<A,X,U,B>,node:mx::Node<A,X,U,B,I>,a:s::State<U>,actor:usize)
    requires inv::well_formed(a),mx::run(lib,node,a,actor).is_some(),
    ensures {
        let out=mx::run(lib,node,a,actor).unwrap();
        &&& forall|n:usize| s::registered(a,n) ==> a.tables[n].dom().subset_of(out.state.tables[n].dom())
        &&& (ph::provision_key(out.receipt).is_some() ==> !a.tables[actor].dom().contains(ph::provision_key(out.receipt).unwrap()))
        &&& (operation_slot(out.receipt).is_some() ==> {
            let slot=operation_slot(out.receipt).unwrap();
            &&& gl::resolve(a,actor,slot.1)==Some(slot.0)
            &&& s::registered(a,slot.0)
            &&& out.state.tables[slot.0].dom().contains(slot.1)
        })
    },
{
    let out=mx::run(lib,node,a,actor).unwrap();
    assert forall|n:usize| s::registered(a,n) implies a.tables[n].dom().subset_of(out.state.tables[n].dom()) by {
        match node {
            mx::Node::Dependent {node}=>match node {
                d::Node::Unit=>{},d::Node::Operation {..}=>{},d::Node::Provision {..}=>{},
            },
            mx::Node::Child {child,..}=>{assert(n!=child);},
        }
    }
    match node {
        mx::Node::Dependent {node}=>match node {d::Node::Operation {..}=>{},d::Node::Provision {..}=>{},_=>{}},
        _=>{},
    }
}

pub proof fn mixed_step<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule)
    requires d::primitive_theory(eq,lib),mx::well_formed(lib,programs,a),live_operations(a),mx::step(lib,programs,a,z,actor,rule),
    ensures live_operations(z),
{
    mx::frame(eq,lib,programs,a,z,actor,rule);
    mx::state_preservation(eq,lib,programs,a,z,actor,rule);
    if rule==r::Rule::Unload {mx::restore_preservation(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);}
    if mx::landing(a,z,rule) {
        run_domains(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor);
    }
    if rule==r::Rule::Unload {mr::restore_domains(a.history,a.state.accumulators[actor],a.state,actor);}
    assert forall|i:int| 0<=i<a.history.len() implies #[trigger] a.history[i]==z.history[i] by {}
    assert forall|n:usize| s::registered(z.state,n) && z.state.accumulators[n].len()>0 implies {
        &&& stable_resolution(a.state,z.state,n)
        &&& forall|key:Port| gl::resolve(a.state,n,key).is_some()
            && a.state.tables[gl::resolve(a.state,n,key).unwrap()].dom().contains(key) ==> {
                let provider=gl::resolve(a.state,n,key).unwrap();
                &&& s::registered(z.state,provider)
                &&& z.state.tables[provider].dom().contains(key)
            }
        &&& (z.state.accumulators[n]==a.state.accumulators[n]
            || (z.state.accumulators[n]==a.state.accumulators[n].push(a.history.len())
                && z.history.len()==a.history.len()+1
                && (operation_slot(z.history.last().landed.receipt).is_some() ==> {
                    let slot=operation_slot(z.history.last().landed.receipt).unwrap();
                    &&& gl::resolve(z.state,n,slot.1)==Some(slot.0)
                    &&& s::registered(z.state,slot.0)
                    &&& z.state.tables[slot.0].dom().contains(slot.1)
                })
                && (ph::provision_key(z.history.last().landed.receipt).is_some()
                    ==> !a.state.tables[n].dom().contains(ph::provision_key(z.history.last().landed.receipt).unwrap()))))
    } by {
        assert(s::registered(a.state,n));
        if n==actor {assert(rule!=r::Rule::Begin && rule!=r::Rule::Unload && rule!=r::Rule::Insert && rule!=r::Rule::Remove);}
        assert(stable_resolution(a.state,z.state,n));
        assert forall|key:Port| gl::resolve(a.state,n,key).is_some()
            && a.state.tables[gl::resolve(a.state,n,key).unwrap()].dom().contains(key) implies {
                let provider=gl::resolve(a.state,n,key).unwrap();
                &&& s::registered(z.state,provider)
                &&& z.state.tables[provider].dom().contains(key)
            } by {
            let provider=gl::resolve(a.state,n,key).unwrap();
            same_resolution(a.state,z.state,n,key);
            gl::resolution_sound(a.state,n,key);
            gl::resolution_sound(z.state,n,key);
            if mx::landing(a,z,rule) {
                let out=mx::entry(lib,programs,a,actor).landed;
                assert(a.state.tables[provider].dom().subset_of(out.state.tables[provider].dom()));
                assert(z.state.tables[provider]==out.state.tables[provider]);
            } else {
                if rule==r::Rule::Unload && provider==actor {
                    assert(n!=actor);
                    let b=Binding {key:key.key,realm:key.realm,provider};
                    assert(a.state.control.fibers[n].committed.contains(b));
                    assert(a.state.control.fibers[n].phase!=Phase::Inactive);
                    assert(r::relied(a.state.control,actor));
                    assert(false);
                }
                match rule {r::Rule::Insert | r::Rule::Remove=>{assert(provider!=actor);},_=>{}}
                assert(a.state.tables[provider].dom()==z.state.tables[provider].dom());
            }
        }
        if mx::landing(a,z,rule) {
            if n==actor {
                let out=mx::entry(lib,programs,a,actor).landed;
                assert(z.history.last().landed==out);
                if operation_slot(out.receipt).is_some() {
                    let slot=operation_slot(out.receipt).unwrap();
                    same_resolution(a.state,z.state,n,slot.1);
                    gl::resolution_sound(z.state,n,slot.1);
                    assert(z.state.tables[slot.0]==out.state.tables[slot.0]);
                }
            }
        } else {assert(z.state.accumulators[n]==a.state.accumulators[n]);}
    }
    journal_preservation(a,z);
}

pub proof fn fresh_step<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:fs::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule,choice:Option<usize>)
    requires crate::observational_grammar::primitive_theory(eq,lib),fs::well_formed(lib,programs,a),live_operations(a),fs::step(lib,programs,a,z,actor,rule,choice),
    ensures live_operations(z),
{
    fs::frame(eq,lib,programs,a,z,actor,rule,choice);
    fs::state_preservation(eq,lib,programs,a,z,actor,rule,choice);
    if rule==r::Rule::Unload {fs::restore_preservation(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);}
    if mx::landing(a,z,rule) {
        let node=fg::instantiate(programs(actor)(a.current[actor].unwrap()),choice).unwrap();
        assert(mx::run(lib,node,a.state,actor).is_some());
        run_domains(lib,node,a.state,actor);
    }
    if rule==r::Rule::Unload {mr::restore_domains(a.history,a.state.accumulators[actor],a.state,actor);}
    assert forall|i:int| 0<=i<a.history.len() implies #[trigger] a.history[i]==z.history[i] by {}
    assert forall|n:usize| s::registered(z.state,n) && z.state.accumulators[n].len()>0 implies {
        &&& stable_resolution(a.state,z.state,n)
        &&& forall|key:Port| gl::resolve(a.state,n,key).is_some()
            && a.state.tables[gl::resolve(a.state,n,key).unwrap()].dom().contains(key) ==> {
                let provider=gl::resolve(a.state,n,key).unwrap();
                &&& s::registered(z.state,provider)
                &&& z.state.tables[provider].dom().contains(key)
            }
        &&& (z.state.accumulators[n]==a.state.accumulators[n]
            || (z.state.accumulators[n]==a.state.accumulators[n].push(a.history.len())
                && z.history.len()==a.history.len()+1
                && (operation_slot(z.history.last().landed.receipt).is_some() ==> {
                    let slot=operation_slot(z.history.last().landed.receipt).unwrap();
                    &&& gl::resolve(z.state,n,slot.1)==Some(slot.0)
                    &&& s::registered(z.state,slot.0)
                    &&& z.state.tables[slot.0].dom().contains(slot.1)
                })
                && (ph::provision_key(z.history.last().landed.receipt).is_some()
                    ==> !a.state.tables[n].dom().contains(ph::provision_key(z.history.last().landed.receipt).unwrap()))))
    } by {
        assert(s::registered(a.state,n));
        if n==actor {assert(rule!=r::Rule::Begin && rule!=r::Rule::Unload && rule!=r::Rule::Insert && rule!=r::Rule::Remove);}
        assert(stable_resolution(a.state,z.state,n));
        assert forall|key:Port| gl::resolve(a.state,n,key).is_some()
            && a.state.tables[gl::resolve(a.state,n,key).unwrap()].dom().contains(key) implies {
                let provider=gl::resolve(a.state,n,key).unwrap();
                &&& s::registered(z.state,provider)
                &&& z.state.tables[provider].dom().contains(key)
            } by {
            let provider=gl::resolve(a.state,n,key).unwrap();
            same_resolution(a.state,z.state,n,key);
            gl::resolution_sound(a.state,n,key);
            gl::resolution_sound(z.state,n,key);
            if mx::landing(a,z,rule) {
                let out=fs::entry(lib,programs,a,actor,choice).landed;
                assert(a.state.tables[provider].dom().subset_of(out.state.tables[provider].dom()));
                assert(z.state.tables[provider]==out.state.tables[provider]);
            } else {
                if rule==r::Rule::Unload && provider==actor {
                    assert(n!=actor);
                    let b=Binding {key:key.key,realm:key.realm,provider};
                    assert(a.state.control.fibers[n].committed.contains(b));
                    assert(a.state.control.fibers[n].phase!=Phase::Inactive);
                    assert(r::relied(a.state.control,actor));
                    assert(false);
                }
                match rule {r::Rule::Insert | r::Rule::Remove=>{assert(provider!=actor);},_=>{}}
                assert(a.state.tables[provider].dom()==z.state.tables[provider].dom());
            }
        }
        if mx::landing(a,z,rule) {
            if n==actor {
                let out=fs::entry(lib,programs,a,actor,choice).landed;
                assert(z.history.last().landed==out);
                if operation_slot(out.receipt).is_some() {
                    let slot=operation_slot(out.receipt).unwrap();
                    same_resolution(a.state,z.state,n,slot.1);
                    gl::resolution_sound(z.state,n,slot.1);
                    assert(z.state.tables[slot.0]==out.state.tables[slot.0]);
                }
            }
        } else {assert(z.state.accumulators[n]==a.state.accumulators[n]);}
    }
    journal_preservation(a,z);
}

proof fn mixed_execution<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires d::primitive_theory(eq,lib),mx::execution(lib,programs,states,labels),mx::well_formed(lib,programs,states.first()),live_operations(states.first()),
    ensures forall|i:int| 0<=i<states.len() ==> live_operations(states[i]),
    decreases labels.len(),
{
    if labels.len()>0 {
        let before=states.drop_last();let steps=labels.drop_last();
        assert(mx::execution(lib,programs,before,steps)) by {
            assert forall|i:int| 0<=i<steps.len() implies mx::step(lib,programs,before[i],before[i+1],steps[i].0,steps[i].1) by {}
        }
        mixed_execution(eq,lib,programs,before,steps);
        mx::execution_preservation(eq,lib,programs,states,labels);
        mixed_step(eq,lib,programs,before.last(),states.last(),labels.last().0,labels.last().1);
        assert forall|i:int| 0<=i<states.len() implies live_operations(states[i]) by {
            if i<before.len() {assert(before[i]==states[i]);} else {assert(i==states.len()-1);}
        }
    }
}

proof fn fresh_execution<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:fs::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<fs::Label>)
    requires crate::observational_grammar::primitive_theory(eq,lib),fs::execution(lib,programs,states,labels),fs::well_formed(lib,programs,states.first()),live_operations(states.first()),
    ensures forall|i:int| 0<=i<states.len() ==> live_operations(states[i]),
    decreases labels.len(),
{
    if labels.len()>0 {
        let before=states.drop_last();let steps=labels.drop_last();
        assert(fs::execution(lib,programs,before,steps)) by {
            assert forall|i:int| 0<=i<steps.len() implies fs::step(lib,programs,before[i],before[i+1],steps[i].0,steps[i].1,steps[i].2) by {}
        }
        fresh_execution(eq,lib,programs,before,steps);
        fs::execution_preservation(eq,lib,programs,states,labels);
        fresh_step(eq,lib,programs,before.last(),states.last(),labels.last().0,labels.last().1,labels.last().2);
        assert forall|i:int| 0<=i<states.len() implies live_operations(states[i]) by {
            if i<before.len() {assert(before[i]==states[i]);} else {assert(i==states.len()-1);}
        }
    }
}

pub proof fn mixed_from_empty<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires d::primitive_theory(eq,lib),mx::execution(lib,programs,states,labels),states.first()==mx::empty::<U,I>(),
    ensures forall|i:int| 0<=i<states.len() ==> live_operations(states[i]),
{
    mx::empty_well_formed(lib,programs);
    mixed_execution(eq,lib,programs,states,labels);
}

pub proof fn fresh_from_empty<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:fs::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<fs::Label>)
    requires crate::observational_grammar::primitive_theory(eq,lib),fs::execution(lib,programs,states,labels),states.first()==fs::empty::<U,I>(),
    ensures forall|i:int| 0<=i<states.len() ==> live_operations(states[i]),
{
    fs::empty_well_formed(lib,programs);
    fresh_execution(eq,lib,programs,states,labels);
}

}
