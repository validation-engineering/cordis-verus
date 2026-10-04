//! Preservation from rule guards and local effect footprints.
//!
//! Callback admissibility constrains the changed fields of each actual map;
//! it does not assert that the complete successor is already well formed.
#[cfg(verus_keep_ghost)]
use crate::{refinement as c, semantics as s, Binding, Phase, Port};
use vstd::prelude::*;

verus! {

pub open spec fn structural(s:c::State) -> bool {
    &&& exists|bound:nat| c::name_bound(s,bound)
    &&& forall|n:usize| c::registered(s,n) ==> match s.fibers[n].parent {Some(p)=>c::registered(s,p),None=>true}
    &&& exists|rank:spec_fn(usize)->nat| c::parent_ranking(s,rank)
    &&& forall|n:usize,m:usize,p:Port| c::registered(s,n) && c::registered(s,m)
        && s.fibers[n].provisions.contains(p) && s.fibers[m].provisions.contains(p) ==> n == m
}

/// Keep the existential ranking witness separate from declaration uniqueness.
/// All lambda arguments retain the original usize domain; no cross-domain
/// function equality is used when the inserted name receives its fresh rank.
proof fn control_parent_ranking(a:c::State,z:c::State,n:usize,rule:c::Rule,rank:spec_fn(usize)->nat)
    requires c::well_formed(a),c::step(a,z,n,rule),c::parent_ranking(a,rank),
    ensures exists|next_rank:spec_fn(usize)->nat| c::parent_ranking(z,next_rank),
{
    if rule==c::Rule::Insert {
        let inserted_rank=match z.fibers[n].parent {Some(p)=>rank(p)+1,None=>0nat};
        let next_rank:spec_fn(usize)->nat=|m:usize|if m==n {inserted_rank}else{rank(m)};
        assert(next_rank(n)==inserted_rank);
        assert(c::parent_ranking(z,next_rank)) by {
            assert forall|m:usize| c::registered(z,m) implies match z.fibers[m].parent {
                Some(p)=>next_rank(p)<next_rank(m),None=>true,
            } by {
                if m==n {
                    if let Some(p)=z.fibers[n].parent {
                        assert(c::registered(a,p));
                        assert(p!=n);
                        assert(next_rank(p)==rank(p));
                        assert(inserted_rank==rank(p)+1);
                    }
                } else {
                    assert(c::registered(a,m));
                    assert(a.fibers[m]==z.fibers[m]);
                    assert(next_rank(m)==rank(m));
                    if let Some(p)=z.fibers[m].parent {
                        assert(c::registered(a,p));
                        assert(p!=n);
                        assert(next_rank(p)==rank(p));
                        assert(rank(p)<rank(m));
                    }
                }
            }
        }
        assert(exists|r:spec_fn(usize)->nat|c::parent_ranking(z,r));
    } else {
        assert(c::parent_ranking(z,rank)) by {
            assert forall|m:usize| c::registered(z,m) implies match z.fibers[m].parent {
                Some(p)=>rank(p)<rank(m),None=>true,
            } by {
                assert(c::registered(a,m));
                assert(z.fibers[m].parent==a.fibers[m].parent);
                if let Some(p)=z.fibers[m].parent {assert(rank(p)<rank(m));}
            }
        }
        assert(exists|r:spec_fn(usize)->nat|c::parent_ranking(z,r));
    }
}

#[verifier::rlimit(15)]
pub proof fn control_structure(a:c::State,z:c::State,n:usize,rule:c::Rule)
    requires c::well_formed(a), c::step(a,z,n,rule),
    ensures structural(z),
{
    let bound = choose|bound:nat| c::name_bound(a,bound);
    let rank = choose|rank:spec_fn(usize)->nat| c::parent_ranking(a,rank);
    if rule == c::Rule::Insert {
        let next_bound = bound + n as nat + 1;
        assert(c::name_bound(z,next_bound)) by {
            assert forall|m:usize| c::registered(z,m) implies m < next_bound by {
                if m != n { assert(c::registered(a,m)); }
            }
        }
        assert(exists|b:nat|c::name_bound(z,b));
    } else {
        assert(c::name_bound(z,bound)) by {
            assert forall|m:usize| c::registered(z,m) implies m < bound by { assert(c::registered(a,m)); }
        }
        assert(exists|b:nat|c::name_bound(z,b));
    }
    control_parent_ranking(a,z,n,rule,rank);
    assert forall|m:usize| c::registered(z,m) implies match z.fibers[m].parent {
        Some(p) => c::registered(z,p), None => true,
    } by {
        if m == n && rule == c::Rule::Insert { }
        else {
            assert(c::registered(a,m));
            assert(z.fibers[m].parent == a.fibers[m].parent);
            if let Some(p) = z.fibers[m].parent {
                assert(c::registered(a,p));
                if rule == c::Rule::Remove { assert(p != n); }
            }
        }
    }
    assert forall|m:usize,k:usize,p:Port| c::registered(z,m) && c::registered(z,k)
        && z.fibers[m].provisions.contains(p) && z.fibers[k].provisions.contains(p) implies m == k by {
        if rule == c::Rule::Insert && m == n && k != n {
            assert(c::registered(a,k)); assert(a.fibers[k].provisions.contains(p));
        } else if rule == c::Rule::Insert && k == n && m != n {
            assert(c::registered(a,m)); assert(a.fibers[m].provisions.contains(p));
        } else if m != k {
            assert(c::registered(a,m)); assert(c::registered(a,k));
            assert(a.fibers[m].provisions.contains(p)); assert(a.fibers[k].provisions.contains(p));
        }
    }
}

#[verifier::rlimit(20)]
pub proof fn control_preservation(a:c::State,z:c::State,n:usize,rule:c::Rule)
    requires c::well_formed(a), c::step(a,z,n,rule),
    ensures c::well_formed(z),
{
    control_structure(a,z,n,rule);
    assert forall|m:usize,b:Binding| c::registered(z,m) && z.fibers[m].committed.contains(b) implies {
        &&& z.fibers[m].phase != Phase::Inactive
        &&& z.fibers[m].dependencies.contains(Port {key:b.key,realm:b.realm})
        &&& c::registered(z,b.provider) && z.fibers[b.provider].phase != Phase::Inactive
        &&& z.fibers[b.provider].provisions.contains(Port {key:b.key,realm:b.realm})
        &&& b.provider != m
    } by {
        if rule == c::Rule::Begin && m == n {
            assert(c::publishes(a,Port {key:b.key,realm:b.realm},b.provider));
            assert(b.provider != n);
        } else {
            assert(c::registered(a,m)); assert(a.fibers[m].committed.contains(b));
            assert(c::registered(a,b.provider)); assert(a.fibers[b.provider].phase != Phase::Inactive);
            if rule == c::Rule::Remove { assert(b.provider != n); }
            if rule == c::Rule::Unload && b.provider == n {
                assert(m != n);
                assert(c::relied(a,n));
            }
        }
    }
    assert forall|m:usize,p:Port| c::registered(z,m) && z.fibers[m].phase != Phase::Inactive
        && z.fibers[m].dependencies.contains(p) implies exists|b:Binding|
            z.fibers[m].committed.contains(b) && b.key == p.key && b.realm == p.realm by {
        if rule == c::Rule::Begin && m == n { }
        else {
            assert(c::registered(a,m)); assert(a.fibers[m].phase != Phase::Inactive);
            let b = choose|b:Binding| a.fibers[m].committed.contains(b) && b.key == p.key && b.realm == p.realm;
            assert(z.fibers[m].committed.contains(b));
        }
    }
    assert forall|m:usize,x:Binding,y:Binding| c::registered(z,m)
        && z.fibers[m].committed.contains(x) && z.fibers[m].committed.contains(y)
        && x.key == y.key && x.realm == y.realm implies x.provider == y.provider by {
        if rule == c::Rule::Begin && m == n {
            let p = Port {key:x.key,realm:x.realm};
            assert(c::publishes(a,p,x.provider)); assert(c::publishes(a,p,y.provider));
            assert(a.fibers[x.provider].provisions.contains(p));
            assert(a.fibers[y.provider].provisions.contains(p));
        } else { assert(c::registered(a,m)); assert(a.fibers[m].committed.contains(x)); assert(a.fibers[m].committed.contains(y)); }
    }}

pub open spec fn well_formed<V>(a:s::State<V>) -> bool {
    c::well_formed(a.control) && s::shaped(a)
}

/// Confinement alone permits an out-of-interface write to the owner's table.
/// The extra local bound is the component typing obligation of Definition 48.
pub open spec fn table_map<V>(a:s::State<V>,z:s::State<V>,actor:usize) -> bool {
    s::confined_write(a,z,actor)
        && z.tables[actor].dom().subset_of(a.control.fibers[actor].provisions)
}

/// The constructor fixes only the new payload slots; all existing slots are
/// framed. No global successor invariant is assumed here.
pub open spec fn insert_map<V>(a:s::State<V>,z:s::State<V>,child:usize) -> bool {
    &&& c::step(a.control,z.control,child,c::Rule::Insert)
    &&& z.tables == a.tables.insert(child,IMap::empty())
    &&& z.effects == a.effects.insert(child,z.effects[child])
    &&& z.iterators == a.iterators.insert(child,None)
    &&& z.accumulators == a.accumulators.insert(child,Seq::empty())
}

pub open spec fn child_map<V>(a:s::State<V>,z:s::State<V>,actor:usize,child:usize) -> bool {
    insert_map(a,z,child) && z.control.fibers[child].parent == Some(actor)
}

pub proof fn insert_preservation<V>(a:s::State<V>,z:s::State<V>,child:usize)
    requires well_formed(a),insert_map(a,z,child),
    ensures well_formed(z),
{
    control_preservation(a.control,z.control,child,c::Rule::Insert);
    assert(z.control.fibers.dom() =~= a.control.fibers.dom().insert(child)) by {
        assert forall|n:usize| z.control.fibers.dom().contains(n) == a.control.fibers.dom().insert(child).contains(n) by {
            if n != child { assert(c::registered(a.control,n) == c::registered(z.control,n)); }
        }
    }
    assert forall|n:usize| s::registered(z,n) implies {
        &&& z.tables[n].dom().subset_of(z.control.fibers[n].provisions)
        &&& (z.control.fibers[n].phase == Phase::Inactive ==> z.iterators[n].is_none()
            && z.accumulators[n].len() == 0 && z.control.fibers[n].committed.is_empty())
        &&& (z.control.fibers[n].phase == Phase::Loading ==> z.iterators[n].is_some())
        &&& (z.control.fibers[n].phase == Phase::Active || z.control.fibers[n].phase == Phase::Unloading
            ==> z.iterators[n].is_none())
    } by {
        if n != child { assert(s::registered(a,n)); assert(a.control.fibers[n] == z.control.fibers[n]); }
    }
}

pub open spec fn forward_map<V>(a:s::State<V>,z:s::State<V>,actor:usize) -> bool {
    table_map(a,z,actor) || exists|child:usize| child_map(a,z,actor,child)
}

/// A recovery may write interface values or retire a child. Either choice keeps
/// every phase, declaration, commitment and iterator fixed.
pub open spec fn inverse_map<V>(a:s::State<V>,z:s::State<V>,actor:usize) -> bool {
    table_map(a,z,actor) || exists|child:usize| s::child_retire(a,z,child)
}

pub proof fn table_preservation<V>(a:s::State<V>,z:s::State<V>,actor:usize)
    requires well_formed(a), s::registered(a,actor), table_map(a,z,actor),
    ensures well_formed(z),
{
    assert forall|n:usize| s::registered(z,n) implies {
        &&& z.tables[n].dom().subset_of(z.control.fibers[n].provisions)
        &&& (z.control.fibers[n].phase == Phase::Inactive ==> z.iterators[n].is_none()
            && z.accumulators[n].len() == 0 && z.control.fibers[n].committed.is_empty())
        &&& (z.control.fibers[n].phase == Phase::Loading ==> z.iterators[n].is_some())
        &&& (z.control.fibers[n].phase == Phase::Active || z.control.fibers[n].phase == Phase::Unloading
            ==> z.iterators[n].is_none())
    } by { assert(s::registered(a,n)); if n != actor { assert(a.tables[n].dom() == z.tables[n].dom()); } }
}

pub proof fn child_preservation<V>(a:s::State<V>,z:s::State<V>,actor:usize,child:usize)
    requires well_formed(a), child_map(a,z,actor,child),
    ensures well_formed(z), s::child_insert(a,z,actor,child),
{
    control_preservation(a.control,z.control,child,c::Rule::Insert);
    s::lift_kernel_child_effect(a,z.control,actor,child,z.effects[child]);
    assert(z == s::extend_child(a,z.control,child,z.effects[child]));
}

pub proof fn retire_preservation<V>(a:s::State<V>,z:s::State<V>,child:usize)
    requires well_formed(a), s::child_retire(a,z,child),
    ensures well_formed(z),
{
    control_preservation(a.control,z.control,child,c::Rule::Retire);
    assert(a.control.fibers.dom() =~= z.control.fibers.dom()) by {
        assert forall|n:usize| a.control.fibers.dom().contains(n) == z.control.fibers.dom().contains(n) by {
            if n != child { assert(c::registered(a.control,n) == c::registered(z.control,n)); }
        }
    }
    assert forall|n:usize| s::registered(z,n) implies {
        &&& z.tables[n].dom().subset_of(z.control.fibers[n].provisions)
        &&& (z.control.fibers[n].phase == Phase::Inactive ==> z.iterators[n].is_none()
            && z.accumulators[n].len() == 0 && z.control.fibers[n].committed.is_empty())
        &&& (z.control.fibers[n].phase == Phase::Loading ==> z.iterators[n].is_some())
        &&& (z.control.fibers[n].phase == Phase::Active || z.control.fibers[n].phase == Phase::Unloading
            ==> z.iterators[n].is_none())
    } by { assert(s::registered(a,n)); }
}

/// The effect primitive retains the installed actor and every old commitment.
/// Newly registered children are Inactive and have no commitment.
pub open spec fn installation_frame<V>(a:s::State<V>,z:s::State<V>) -> bool {
    &&& a.control.fibers.dom().subset_of(z.control.fibers.dom())
    &&& forall|n:usize| s::registered(a,n) ==> {
        &&& c::interface_same(a.control.fibers[n],z.control.fibers[n])
        &&& a.control.fibers[n].phase == z.control.fibers[n].phase
        &&& a.control.fibers[n].committed == z.control.fibers[n].committed
    }
    &&& forall|n:usize| s::registered(z,n) && !s::registered(a,n)
        ==> z.control.fibers[n].phase == Phase::Inactive && z.control.fibers[n].committed.is_empty()
}

pub proof fn forward_preservation<V>(a:s::State<V>,z:s::State<V>,actor:usize)
    requires well_formed(a),s::registered(a,actor),forward_map(a,z,actor),
    ensures well_formed(z), installation_frame(a,z),
        forall|n:usize| s::registered(a,n) ==> a.control.fibers[n] == z.control.fibers[n],
{
    if table_map(a,z,actor) { table_preservation(a,z,actor); }
    else {
        let child = choose|child:usize| child_map(a,z,actor,child);
        child_preservation(a,z,actor,child);
        assert(a.control.fibers.dom().subset_of(z.control.fibers.dom())) by {
            assert forall|n:usize| s::registered(a,n) implies s::registered(z,n) by { assert(n != child); }
        }
    }
    assert forall|n:usize| s::registered(a,n) implies {
        &&& c::interface_same(a.control.fibers[n],z.control.fibers[n])
        &&& a.control.fibers[n].phase == z.control.fibers[n].phase
        &&& a.control.fibers[n].committed == z.control.fibers[n].committed
    } by { }
}

pub proof fn inverse_preservation<V>(a:s::State<V>,z:s::State<V>,actor:usize)
    requires well_formed(a),s::registered(a,actor),inverse_map(a,z,actor),
    ensures well_formed(z), installation_frame(a,z), a.control.fibers.dom() == z.control.fibers.dom(),
{
    if table_map(a,z,actor) { table_preservation(a,z,actor); }
    else {
        let child = choose|child:usize| s::child_retire(a,z,child);
        retire_preservation(a,z,child);
        assert(a.control.fibers.dom() =~= z.control.fibers.dom()) by {
            assert forall|n:usize| s::registered(a,n) == s::registered(z,n) by { }
        }
    }
    assert forall|n:usize| s::registered(a,n) implies {
        &&& c::interface_same(a.control.fibers[n],z.control.fibers[n])
        &&& a.control.fibers[n].phase == z.control.fibers[n].phase
        &&& a.control.fibers[n].committed == z.control.fibers[n].committed
    } by { }
}

/// This predicate follows the actual recursive accumulator evaluation. Each
/// premise is a local map footprint, not a complete-state preservation claim.
pub open spec fn admissible_restore<V>(model:s::Model<V>,tokens:Seq<nat>,a:s::State<V>,actor:usize) -> bool
    decreases tokens.len(),
{
    tokens.len() == 0 || {
        let z = (model.undo)(tokens.last(),a);
        inverse_map(a,z,actor) && admissible_restore(model,tokens.drop_last(),z,actor)
    }
}

pub proof fn frame_composes<V>(a:s::State<V>,b:s::State<V>,z:s::State<V>)
    requires installation_frame(a,b),installation_frame(b,z),
    ensures installation_frame(a,z),
{
    assert forall|n:usize| s::registered(a,n) implies {
        &&& c::interface_same(a.control.fibers[n],z.control.fibers[n])
        &&& a.control.fibers[n].phase == z.control.fibers[n].phase
        &&& a.control.fibers[n].committed == z.control.fibers[n].committed
    } by { assert(s::registered(b,n)); }
    assert forall|n:usize| s::registered(z,n) && !s::registered(a,n)
        implies z.control.fibers[n].phase == Phase::Inactive && z.control.fibers[n].committed.is_empty() by {
        if s::registered(b,n) { assert(b.control.fibers[n].phase == Phase::Inactive); }
    }
}

pub proof fn restore_preservation<V>(model:s::Model<V>,tokens:Seq<nat>,a:s::State<V>,actor:usize)
    requires well_formed(a),s::registered(a,actor),admissible_restore(model,tokens,a,actor),
    ensures well_formed(s::restore(model,tokens,a)), installation_frame(a,s::restore(model,tokens,a)),
        a.control.fibers.dom() == s::restore(model,tokens,a).control.fibers.dom(),
    decreases tokens.len(),
{
    if tokens.len() > 0 {
        let z = (model.undo)(tokens.last(),a);
        inverse_preservation(a,z,actor);
        assert(s::registered(z,actor));
        restore_preservation(model,tokens.drop_last(),z,actor);
        frame_composes(a,z,s::restore(model,tokens.drop_last(),z));
    }
}

pub proof fn shaped_edit<V>(a:s::State<V>,n:usize,phase:Phase,view:ISet<Binding>,iterator:Option<nat>,acc:Seq<nat>)
    requires s::shaped(a),s::registered(a,n),
        phase == Phase::Inactive ==> iterator.is_none() && acc.len() == 0 && view.is_empty(),
        phase == Phase::Loading ==> iterator.is_some(),
        phase == Phase::Active || phase == Phase::Unloading ==> iterator.is_none(),
    ensures s::shaped(s::edit(a,n,phase,view,iterator,acc)),
{
    let z = s::edit(a,n,phase,view,iterator,acc);
    assert(a.control.fibers.dom() =~= z.control.fibers.dom());
    assert(a.iterators.dom() =~= z.iterators.dom());
    assert(a.accumulators.dom() =~= z.accumulators.dom());
    assert forall|m:usize| s::registered(z,m) implies {
        &&& z.tables[m].dom().subset_of(z.control.fibers[m].provisions)
        &&& (z.control.fibers[m].phase == Phase::Inactive ==> z.iterators[m].is_none()
            && z.accumulators[m].len() == 0 && z.control.fibers[m].committed.is_empty())
        &&& (z.control.fibers[m].phase == Phase::Loading ==> z.iterators[m].is_some())
        &&& (z.control.fibers[m].phase == Phase::Active || z.control.fibers[m].phase == Phase::Unloading
            ==> z.iterators[m].is_none())
    } by { if m != n { assert(s::registered(a,m)); } }
}

/// An actual table target is a sound control target even with partial provision.
/// The reverse implication needs total publication; preservation does not.
pub proof fn partial_target_sound<V>(a:s::State<V>,n:usize,view:ISet<Binding>)
    requires s::shaped(a),s::target(a,n,view),
    ensures c::target(a.control,n,view),
{
    assert forall|b:Binding| view.contains(b) implies a.control.fibers[n].dependencies.contains(Port{key:b.key,realm:b.realm})
        && c::publishes(a.control,Port{key:b.key,realm:b.realm},b.provider) by {
        assert(s::publishes(a,Port{key:b.key,realm:b.realm},b.provider));
        assert(a.tables[b.provider].dom().subset_of(a.control.fibers[b.provider].provisions));
    }
}

/// Every actual forward result is checked when used. Immediate diversion needs
/// no forward map; landed diversion retains and checks the actual result.
pub open spec fn admissible_step<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,n:usize,rule:c::Rule) -> bool {
    match rule {
        c::Rule::Insert => insert_map(a,z,n),
        c::Rule::Iter | c::Rule::Finish => forward_map(a,(model.iterate)(n,a.iterators[n].unwrap(),a).state,n),
        c::Rule::Divert => z == s::edit(a,n,Phase::Unloading,a.control.fibers[n].committed,None,a.accumulators[n])
            || forward_map(a,(model.iterate)(n,a.iterators[n].unwrap(),a).state,n),
        c::Rule::Unload => admissible_restore(model,a.accumulators[n],a,n),
        _ => true,
    }
}

pub proof fn begin_preservation<V>(a:s::State<V>,z:s::State<V>,n:usize)
    requires well_formed(a),s::registered(a,n),a.control.fibers[n].phase == Phase::Inactive,
        s::target(a,n,z.control.fibers[n].committed),
        z == s::edit(a,n,Phase::Loading,z.control.fibers[n].committed,Some(a.effects[n]),Seq::empty()),
    ensures well_formed(z),
{
    partial_target_sound(a,n,z.control.fibers[n].committed);
    assert(c::frame(a.control,z.control,n)) by {
        assert forall|m:usize| m != n implies c::registered(a.control,m) == c::registered(z.control,m)
            && (c::registered(a.control,m) ==> a.control.fibers[m] == z.control.fibers[m]) by { }
    }
    assert(c::step(a.control,z.control,n,c::Rule::Begin));
    control_preservation(a.control,z.control,n,c::Rule::Begin);
    shaped_edit(a,n,Phase::Loading,z.control.fibers[n].committed,Some(a.effects[n]),Seq::empty());
}

pub proof fn finish_preservation<V>(a:s::State<V>,context:s::State<V>,n:usize,acc:Seq<nat>)
    requires well_formed(a),s::registered(a,n),a.control.fibers[n].phase == Phase::Loading,
        s::coherent(a,n),forward_map(a,context,n),
    ensures well_formed(s::edit(context,n,Phase::Active,a.control.fibers[n].committed,None,acc)),
{
    forward_preservation(a,context,n);
    partial_target_sound(a,n,a.control.fibers[n].committed);
    assert(c::coherent(context.control,n)) by {
        assert forall|b:Binding| context.control.fibers[n].committed.contains(b) implies
            context.control.fibers[n].dependencies.contains(Port{key:b.key,realm:b.realm})
            && c::publishes(context.control,Port{key:b.key,realm:b.realm},b.provider) by {
            assert(a.control.fibers[n].committed.contains(b));
            assert(c::registered(a.control,b.provider));
            assert(context.control.fibers[b.provider] == a.control.fibers[b.provider]);
        }
    }
    let z = s::edit(context,n,Phase::Active,a.control.fibers[n].committed,None,acc);
    s::edit_control_phase(context,n,Phase::Active,None,acc);
    control_preservation(context.control,z.control,n,c::Rule::Finish);
    shaped_edit(context,n,Phase::Active,a.control.fibers[n].committed,None,acc);
}

/// Changing a noninactive phase to Unloading is structurally safe independently
/// of publication completeness. Restart is used solely as a safety lemma here;
/// the caller still proves its actual strict-paper Divert or Leave rule.
pub proof fn unloading_edit_preservation<V>(a:s::State<V>,n:usize,acc:Seq<nat>)
    requires well_formed(a),s::registered(a,n),
        a.control.fibers[n].phase == Phase::Loading || a.control.fibers[n].phase == Phase::Active,
    ensures well_formed(s::edit(a,n,Phase::Unloading,a.control.fibers[n].committed,None,acc)),
{
    let z = s::edit(a,n,Phase::Unloading,a.control.fibers[n].committed,None,acc);
    s::edit_control_phase(a,n,Phase::Unloading,None,acc);
    control_preservation(a.control,z.control,n,c::Rule::Restart);
    shaped_edit(a,n,Phase::Unloading,a.control.fibers[n].committed,None,acc);
}

pub proof fn unload_preservation<V>(model:s::Model<V>,a:s::State<V>,n:usize)
    requires well_formed(a),s::registered(a,n),a.control.fibers[n].phase == Phase::Unloading,
        !c::relied(a.control,n),admissible_restore(model,a.accumulators[n],a,n),
    ensures well_formed(s::edit(s::restore(model,a.accumulators[n],a),n,Phase::Inactive,ISet::empty(),None,Seq::empty())),
{
    restore_preservation(model,a.accumulators[n],a,n);
    let context = s::restore(model,a.accumulators[n],a);
    assert(!c::relied(context.control,n)) by {
        if c::relied(context.control,n) {
            let (m,b) = choose|m:usize,b:Binding| c::registered(context.control,m) && m != n
                && context.control.fibers[m].phase != Phase::Inactive
                && context.control.fibers[m].committed.contains(b) && b.provider == n;
            assert(s::registered(a,m));
            assert(a.control.fibers[m].committed == context.control.fibers[m].committed);
            assert(a.control.fibers[m].committed.contains(b));
            assert(c::relied(a.control,n));
        }
    }
    let z = s::edit(context,n,Phase::Inactive,ISet::empty(),None,Seq::empty());
    assert(c::frame(context.control,z.control,n)) by {
        assert forall|m:usize| m != n implies c::registered(context.control,m) == c::registered(z.control,m)
            && (c::registered(context.control,m) ==> context.control.fibers[m] == z.control.fibers[m]) by { }
    }
    assert(c::step(context.control,z.control,n,c::Rule::Unload));
    control_preservation(context.control,z.control,n,c::Rule::Unload);
    shaped_edit(context,n,Phase::Inactive,ISet::empty(),None,Seq::empty());
}

/// Theorem 64 for the value-carrying nine-rule calculus and its locally typed
/// table/child primitives. Partial publication is supported. Recovery and
/// noninterference laws are separate obligations, not needed for type safety.
#[verifier::rlimit(15)]
pub proof fn full_preservation<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,n:usize,rule:c::Rule)
    requires well_formed(a),s::step(model,a,z,n,rule),admissible_step(model,a,z,n,rule),
    ensures well_formed(z),
{
    match rule {
        c::Rule::Insert => { insert_preservation(a,z,n); }
        c::Rule::Retire => { retire_preservation(a,z,n); }
        c::Rule::Remove => {
            control_preservation(a.control,z.control,n,rule);
            assert(z.control.fibers.dom() =~= a.control.fibers.dom().remove(n)) by {
                assert forall|m:usize| z.control.fibers.dom().contains(m)
                    == a.control.fibers.dom().remove(n).contains(m) by {
                    if m != n { assert(c::registered(a.control,m) == c::registered(z.control,m)); }
                }
            }
            assert forall|m:usize| s::registered(z,m) implies {
                &&& z.tables[m].dom().subset_of(z.control.fibers[m].provisions)
                &&& (z.control.fibers[m].phase == Phase::Inactive ==> z.iterators[m].is_none()
                    && z.accumulators[m].len() == 0 && z.control.fibers[m].committed.is_empty())
                &&& (z.control.fibers[m].phase == Phase::Loading ==> z.iterators[m].is_some())
                &&& (z.control.fibers[m].phase == Phase::Active || z.control.fibers[m].phase == Phase::Unloading
                    ==> z.iterators[m].is_none())
            } by { assert(m != n); assert(s::registered(a,m)); }
        }
        c::Rule::Begin => { begin_preservation(a,z,n); }
        c::Rule::Iter => {
            let y = (model.iterate)(n,a.iterators[n].unwrap(),a);
            forward_preservation(a,y.state,n);
            shaped_edit(y.state,n,Phase::Loading,a.control.fibers[n].committed,y.next,a.accumulators[n].push(y.inverse));
            assert(z.control.fibers =~= y.state.control.fibers) by {
                assert forall|m:usize| z.control.fibers.dom().contains(m) implies z.control.fibers[m] == y.state.control.fibers[m] by { }
            }
        }
        c::Rule::Finish => {
            let y = (model.iterate)(n,a.iterators[n].unwrap(),a);
            finish_preservation(a,y.state,n,a.accumulators[n].push(y.inverse));
        }
        c::Rule::Divert => {
            if z == s::edit(a,n,Phase::Unloading,a.control.fibers[n].committed,None,a.accumulators[n]) {
                unloading_edit_preservation(a,n,a.accumulators[n]);
            } else {
                let y = (model.iterate)(n,a.iterators[n].unwrap(),a);
                forward_preservation(a,y.state,n);
                unloading_edit_preservation(y.state,n,a.accumulators[n].push(y.inverse));
            }
        }
        c::Rule::Leave => { unloading_edit_preservation(a,n,a.accumulators[n]); }
        c::Rule::Unload => { unload_preservation(model,a,n); }
        _ => { }
    }
}

/// Labelled executions retain actual intermediate contexts and actual model
/// results. No invariant at intermediate positions is a trace premise.
pub open spec fn execution<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>) -> bool {
    states.len() == labels.len()+1 && forall|i:int| 0 <= i < labels.len() ==>
        s::step(model,states[i],states[i+1],labels[i].0,labels[i].1)
            && admissible_step(model,states[i],states[i+1],labels[i].0,labels[i].1)
}

pub proof fn execution_preservation<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>)
    requires execution(model,states,labels),well_formed(states.first()),
    ensures forall|i:int| 0 <= i < states.len() ==> well_formed(states[i]),
    decreases labels.len(),
{
    if labels.len() == 0 { assert(states.first() == states[0]); }
    else {
        let previous = states.drop_last();
        let previous_labels = labels.drop_last();
        assert(previous.len() == previous_labels.len()+1);
        assert(execution(model,previous,previous_labels)) by {
            assert forall|i:int| 0 <= i < previous_labels.len() implies
                s::step(model,previous[i],previous[i+1],previous_labels[i].0,previous_labels[i].1)
                    && admissible_step(model,previous[i],previous[i+1],previous_labels[i].0,previous_labels[i].1) by { }
        }
        execution_preservation(model,previous,previous_labels);
        let i = labels.len()-1;
        assert(previous[i] == states[i]);
        assert(well_formed(previous[i]));
        assert(well_formed(states[i]));
        full_preservation(model,states[i],states[i+1],labels[i].0,labels[i].1);
        assert forall|j:int| 0 <= j < states.len() implies well_formed(states[j]) by {
            if j < previous.len() { assert(previous[j] == states[j]); }
        }
    }
}

/// Concrete constructor for the initial registry of Definition 58.
pub open spec fn empty<V>() -> s::State<V> {
    s::State {control:c::State{fibers:IMap::empty()},tables:IMap::empty(),effects:IMap::empty(),
        iterators:IMap::empty(),accumulators:IMap::empty()}
}

pub proof fn empty_well_formed<V>()
    ensures well_formed(empty::<V>()),
{
    assert(c::name_bound(empty::<V>().control,0));
    assert(c::parent_ranking(empty::<V>().control,|n:usize| 0nat));
}

pub open spec fn resource_safe<V>(a:s::State<V>) -> bool {
    &&& forall|p:Port,x:usize,y:usize| s::publishes(a,p,x) && s::publishes(a,p,y) ==> x == y
    &&& forall|n:usize,b:Binding| s::registered(a,n) && a.control.fibers[n].committed.contains(b)
        ==> s::registered(a,b.provider) && a.control.fibers[b.provider].phase != Phase::Inactive
}

/// Publication has one source even when tables publish strict subsets of their
/// declarations, and every installed committed provider remains installed.
pub proof fn execution_resource_safety<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>)
    requires execution(model,states,labels),states.first() == empty::<V>(),
    ensures forall|i:int| 0 <= i < states.len() ==> resource_safe(states[i]),
{
    empty_well_formed::<V>();
    execution_preservation(model,states,labels);
    assert forall|i:int| 0 <= i < states.len() implies resource_safe(states[i]) by {
        assert(well_formed(states[i]));
        assert forall|p:Port,x:usize,y:usize| s::publishes(states[i],p,x) && s::publishes(states[i],p,y) implies x == y by {
            assert(states[i].control.fibers[x].provisions.contains(p));
            assert(states[i].control.fibers[y].provisions.contains(p));
        }
    }
}

pub open spec fn erase(a:c::State,n:usize) -> c::State { c::State {fibers:a.fibers.remove(n)} }

/// The control part of a vestigial entry; the value-layer condition additionally
/// requires its table to be empty. Its own declarations need not be empty.
pub open spec fn vestigial(a:c::State,n:usize) -> bool {
    c::registered(a,n) && a.fibers[n].retired && a.fibers[n].phase == Phase::Inactive
        && a.fibers[n].committed.is_empty()
        && forall|m:usize| c::registered(a,m) ==> a.fibers[m].parent != Some(n)
}

pub proof fn vestigial_queries(a:c::State,removed:usize,actor:usize)
    requires vestigial(a,removed),actor != removed,
    ensures (forall|view:ISet<Binding>| c::target(a,actor,view) == c::target(erase(a,removed),actor,view)),
        c::coherent(a,actor) == c::coherent(erase(a,removed),actor),
        c::relied(a,actor) == c::relied(erase(a,removed),actor),
{
    assert forall|p:Port,n:usize| c::publishes(a,p,n) == c::publishes(erase(a,removed),p,n) by { }
    assert forall|view:ISet<Binding>| c::target(a,actor,view) == c::target(erase(a,removed),actor,view) by { }
    if c::relied(a,actor) {
        let (m,b) = choose|m:usize,b:Binding| c::registered(a,m) && m != actor && a.fibers[m].phase != Phase::Inactive
            && a.fibers[m].committed.contains(b) && b.provider == actor;
        assert(m != removed);
        assert(c::registered(erase(a,removed),m));
        assert(erase(a,removed).fibers[m].committed.contains(b));
        assert(c::relied(erase(a,removed),actor));
    }
    if c::relied(erase(a,removed),actor) {
        let (m,b) = choose|m:usize,b:Binding| c::registered(erase(a,removed),m) && m != actor
            && erase(a,removed).fibers[m].phase != Phase::Inactive
            && erase(a,removed).fibers[m].committed.contains(b) && b.provider == actor;
        assert(c::registered(a,m));
        assert(a.fibers[m].committed.contains(b));
        assert(c::relied(a,actor));
    }
}

/// These are precisely the three control observations omitted by Lemma 62:
/// insertion can use the erased parent or conflict with its provision, and
/// removing its parent can become enabled after erasure.
pub open spec fn erasure_compatible(a:c::State,z:c::State,removed:usize,actor:usize,rule:c::Rule) -> bool {
    &&& actor != removed && c::registered(z,removed) && a.fibers[removed] == z.fibers[removed]
    &&& (rule == c::Rule::Insert ==> z.fibers[actor].parent != Some(removed)
        && forall|p:Port| a.fibers[removed].provisions.contains(p) ==> !z.fibers[actor].provisions.contains(p))
    &&& (rule == c::Rule::Remove ==> a.fibers[removed].parent != Some(actor))
}

/// Corrected bidirectional Lemma 62 for all nine control rules. The explicit
/// side conditions exclude the known reachable counterexamples; no rule
/// applicability or successor well-formedness is assumed.
#[verifier::rlimit(15)]
pub proof fn vestigial_control_bisimulation(a:c::State,z:c::State,removed:usize,actor:usize,rule:c::Rule)
    requires vestigial(a,removed),erasure_compatible(a,z,removed,actor,rule),
    ensures c::step(a,z,actor,rule) == c::step(erase(a,removed),erase(z,removed),actor,rule),
{
    let left = erase(a,removed);
    let right = erase(z,removed);
    vestigial_queries(a,removed,actor);
    assert(c::frame(a,z,actor) == c::frame(left,right,actor)) by {
        if c::frame(a,z,actor) {
            assert forall|m:usize| m != actor implies c::registered(left,m) == c::registered(right,m)
                && (c::registered(left,m) ==> left.fibers[m] == right.fibers[m]) by {
                assert(c::registered(a,m) == c::registered(z,m));
                if c::registered(a,m) { assert(a.fibers[m] == z.fibers[m]); }
            }
        } else if c::frame(left,right,actor) {
            assert forall|m:usize| m != actor implies c::registered(a,m) == c::registered(z,m)
                && (c::registered(a,m) ==> a.fibers[m] == z.fibers[m]) by {
                if m != removed { assert(c::registered(left,m) == c::registered(right,m)); }
            }
        }
    }
    assert((a == z) == (left == right)) by {
        if left == right {
            assert(a.fibers =~= z.fibers) by {
                assert forall|m:usize| a.fibers.dom().contains(m) == z.fibers.dom().contains(m) by {
                    if m != removed { assert(left.fibers.dom().contains(m) == right.fibers.dom().contains(m)); }
                }
                assert forall|m:usize| a.fibers.dom().contains(m) implies a.fibers[m] == z.fibers[m] by {
                    if m != removed { assert(left.fibers.dom().contains(m)); assert(left.fibers[m] == right.fibers[m]); }
                }
            }
        }
    }
    if rule == c::Rule::Insert {
        if !c::registered(z,actor) { return; }
        assert((forall|m:usize,p:Port| c::registered(a,m) && a.fibers[m].provisions.contains(p)
            ==> !z.fibers[actor].provisions.contains(p))
            == (forall|m:usize,p:Port| c::registered(left,m) && left.fibers[m].provisions.contains(p)
            ==> !right.fibers[actor].provisions.contains(p))) by {
            if forall|m:usize,p:Port| c::registered(a,m) && a.fibers[m].provisions.contains(p) ==> !z.fibers[actor].provisions.contains(p) {
                assert forall|m:usize,p:Port| c::registered(left,m) && left.fibers[m].provisions.contains(p)
                    implies !right.fibers[actor].provisions.contains(p) by { assert(c::registered(a,m)); }
            } else if forall|m:usize,p:Port| c::registered(left,m) && left.fibers[m].provisions.contains(p) ==> !right.fibers[actor].provisions.contains(p) {
                assert forall|m:usize,p:Port| c::registered(a,m) && a.fibers[m].provisions.contains(p)
                    implies !z.fibers[actor].provisions.contains(p) by {
                    if m != removed {
                        assert(c::registered(left,m));
                        assert(left.fibers[m].provisions.contains(p));
                        assert(!right.fibers[actor].provisions.contains(p));
                    } else { assert(a.fibers[removed].provisions.contains(p)); }
                }
            }
        }
    }
    if rule == c::Rule::Remove {
        assert((forall|m:usize| c::registered(a,m) ==> a.fibers[m].parent != Some(actor))
            == (forall|m:usize| c::registered(left,m) ==> left.fibers[m].parent != Some(actor))) by {
            if forall|m:usize| c::registered(a,m) ==> a.fibers[m].parent != Some(actor) {
                assert forall|m:usize| c::registered(left,m) implies left.fibers[m].parent != Some(actor) by { assert(c::registered(a,m)); }
            } else if forall|m:usize| c::registered(left,m) ==> left.fibers[m].parent != Some(actor) {
                assert forall|m:usize| c::registered(a,m) implies a.fibers[m].parent != Some(actor) by {
                    if m != removed { assert(c::registered(left,m)); }
                }
            }
        }
    }
}

} // verus!
