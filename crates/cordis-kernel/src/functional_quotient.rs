//! Function-valued observations for the full registry representation.
//!
//! Iterator identities are compared by greatest bisimulation; accumulators by
//! their interpreted functions, not token equality or equal journal length.
//! The lifecycle simulation below is restricted to table primitives. Internal
//! child creation/retirement requires additional structural observations: the
//! paper's table observation alone cannot identify those control effects.
//! Function comparisons here use all keys K. Deriving these comparisons from
//! a component's interface S requires a separate outside-S frame argument;
//! inclusion of the underlying state relations does not supply that argument.
#[cfg(verus_keep_ghost)]
use crate::{
    calculus, mixed_observational_runs as rows, observation as o, preservation as p, projection,
    quotient as q, refinement as r, semantics as s, Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {

/// Definition 51, including tables in every lifecycle phase.
pub open spec fn observed<V>(eq:spec_fn(Port,V,V)->bool,a:s::State<V>,b:s::State<V>)->bool {
    o::context_equal(eq,ISet::full(),projection::project(a,ISet::full()),projection::project(b,ISet::full()))
}
pub open spec fn family<V>(model:s::Model<V>,actor:usize)->q::IteratorFamily<s::State<V>,nat> {
    |id:nat,a:s::State<V>| {
        let y=(model.iterate)(actor,id,a);
        q::Iteration {state:y.state,undo:|b:s::State<V>|(model.undo)(y.inverse,b),next:y.next}
    }
}
pub open spec fn iterator_related<V>(eq:spec_fn(Port,V,V)->bool,model:s::Model<V>,actor:usize,left:nat,right:nat)->bool {
    q::iterator_related(|a:s::State<V>,b:s::State<V>|observed(eq,a,b),family(model,actor),left,right)
}
pub open spec fn continuations<V>(eq:spec_fn(Port,V,V)->bool,model:s::Model<V>,actor:usize,left:Option<nat>,right:Option<nat>)->bool {
    q::continuation(|i:nat,j:nat|iterator_related(eq,model,actor,i,j),left,right)
}
pub open spec fn accumulator<V>(model:s::Model<V>,tokens:Seq<nat>)->spec_fn(s::State<V>)->s::State<V> {
    |a:s::State<V>|s::restore(model,tokens,a)
}
pub open spec fn accumulators_related<V>(eq:spec_fn(Port,V,V)->bool,model:s::Model<V>,left:Seq<nat>,right:Seq<nat>)->bool {
    o::related_maps(|a:s::State<V>,b:s::State<V>|observed(eq,a,b),accumulator(model,left),accumulator(model,right))
}
/// Equation 54's function fields are interpreted rather than compared as IDs.
/// Well-formedness is kept separate, just as respect is not automatic reflexivity.
pub open spec fn related<V>(eq:spec_fn(Port,V,V)->bool,model:s::Model<V>,a:s::State<V>,b:s::State<V>)->bool {
    &&& a.control==b.control && observed(eq,a,b)
    &&& forall|n:usize| s::registered(a,n) ==> {
        &&& iterator_related(eq,model,n,a.effects[n],b.effects[n])
        &&& continuations(eq,model,n,a.iterators[n],b.iterators[n])
        &&& accumulators_related(eq,model,a.accumulators[n],b.accumulators[n])
    }
}

pub proof fn observation_equivalence<V>(eq:spec_fn(Port,V,V)->bool)
    requires forall|key:Port| #[trigger] q::key_equivalent(eq,key),
    ensures calculus::equivalence(|a:s::State<V>,b:s::State<V>|observed(eq,a,b)),
{
    assert forall|key:Port| ISet::<Port>::full().contains(key) implies calculus::equivalence(|a:V,b:V|eq(key,a,b)) by {assert(q::key_equivalent(eq,key));}
    o::context_equivalence(eq,ISet::full());
    let table=|a:IMap<Port,V>,b:IMap<Port,V>|o::context_equal(eq,ISet::full(),a,b);
    assert(calculus::equivalence(table));
    assert forall|a:s::State<V>| #[trigger] observed(eq,a,a) by {assert(table(projection::project(a,ISet::full()),projection::project(a,ISet::full())));}
    assert forall|a:s::State<V>,b:s::State<V>| observed(eq,a,b) implies #[trigger] observed(eq,b,a) by {
        assert(table(projection::project(a,ISet::full()),projection::project(b,ISet::full())));
        assert(table(projection::project(b,ISet::full()),projection::project(a,ISet::full())));
    }
    assert forall|a:s::State<V>,b:s::State<V>,c:s::State<V>| #[trigger] observed(eq,a,b) && #[trigger] observed(eq,b,c) implies observed(eq,a,c) by {
        assert(table(projection::project(a,ISet::full()),projection::project(b,ISet::full())));
        assert(table(projection::project(b,ISet::full()),projection::project(c,ISet::full())));
        assert(table(projection::project(a,ISet::full()),projection::project(c,ISet::full())));
    }
}

pub proof fn empty_accumulators<V>(eq:spec_fn(Port,V,V)->bool,model:s::Model<V>)
    ensures accumulators_related(eq,model,Seq::empty(),Seq::empty()),
{ }

/// No pointwise relation between tokens and no equality of stack lengths is
/// required: composing two related denotations preserves their relation.
pub proof fn append_inverse<V>(eq:spec_fn(Port,V,V)->bool,model:s::Model<V>,left:Seq<nat>,right:Seq<nat>,x:nat,y:nat)
    requires accumulators_related(eq,model,left,right),
        o::related_maps(|a:s::State<V>,b:s::State<V>|observed(eq,a,b),
            |a:s::State<V>|(model.undo)(x,a),|a:s::State<V>|(model.undo)(y,a)),
    ensures accumulators_related(eq,model,left.push(x),right.push(y)),
{
    let obs=|a:s::State<V>,b:s::State<V>|observed(eq,a,b);
    let f=|a:s::State<V>|(model.undo)(x,a);let g=|a:s::State<V>|(model.undo)(y,a);
    let h=accumulator(model,left);let j=accumulator(model,right);
    o::compose_related(obs,h,j,f,g);
    assert forall|a:s::State<V>,b:s::State<V>| observed(eq,a,b) implies
        #[trigger] observed(eq,s::restore(model,left.push(x),a),s::restore(model,right.push(y),b)) by {
        assert(left.push(x).drop_last()==left);assert(right.push(y).drop_last()==right);
        assert(obs(crate::foundations::compose(h,f)(a),crate::foundations::compose(j,g)(b)));
    }
}

pub proof fn call_related<V>(eq:spec_fn(Port,V,V)->bool,model:s::Model<V>,actor:usize,left:nat,right:nat,a:s::State<V>,b:s::State<V>)
    requires iterator_related(eq,model,actor,left,right),observed(eq,a,b),
    ensures {
        let x=(model.iterate)(actor,left,a);let y=(model.iterate)(actor,right,b);
        &&& observed(eq,x.state,y.state)
        &&& continuations(eq,model,actor,x.next,y.next)
        &&& o::related_maps(|u:s::State<V>,v:s::State<V>|observed(eq,u,v),
            |u:s::State<V>|(model.undo)(x.inverse,u),|v:s::State<V>|(model.undo)(y.inverse,v))
    },
{
    q::iterator_unfolding(|u:s::State<V>,v:s::State<V>|observed(eq,u,v),family(model,actor),left,right);
    assert(q::iterator_clause(|u:s::State<V>,v:s::State<V>|observed(eq,u,v),family(model,actor),left,right));
    assert(observed(eq,family(model,actor)(left,a).state,family(model,actor)(right,b).state));
}

/// A primitive contract on the fields it can write; no rule or paired successor
/// is mentioned. Value transformations may differ observationally.
pub open spec fn table_frame<V>(a:s::State<V>,z:s::State<V>)->bool {
    &&& a.control==z.control && a.effects==z.effects && a.iterators==z.iterators && a.accumulators==z.accumulators
    &&& (p::well_formed(a) ==> p::well_formed(z))
}
pub open spec fn table_primitives<V>(model:s::Model<V>)->bool {
    &&& forall|n:usize,id:nat,a:s::State<V>| p::well_formed(a) && s::registered(a,n)
        ==> table_frame(a,#[trigger] (model.iterate)(n,id,a).state)
    &&& forall|token:nat,a:s::State<V>| p::well_formed(a)
        ==> table_frame(a,#[trigger] (model.undo)(token,a))
}

pub proof fn frames_related<V>(eq:spec_fn(Port,V,V)->bool,model:s::Model<V>,a:s::State<V>,b:s::State<V>,x:s::State<V>,y:s::State<V>)
    requires related(eq,model,a,b),table_frame(a,x),table_frame(b,y),observed(eq,x,y),
    ensures related(eq,model,x,y),
{
    assert forall|n:usize| s::registered(x,n) implies {
        &&& iterator_related(eq,model,n,x.effects[n],y.effects[n])
        &&& continuations(eq,model,n,x.iterators[n],y.iterators[n])
        &&& accumulators_related(eq,model,x.accumulators[n],y.accumulators[n])
    } by {assert(s::registered(a,n));}
}

pub proof fn restore_frame<V>(model:s::Model<V>,tokens:Seq<nat>,a:s::State<V>)
    requires table_primitives(model),p::well_formed(a),
    ensures table_frame(a,s::restore(model,tokens,a)),p::well_formed(s::restore(model,tokens,a)),
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let b=(model.undo)(tokens.last(),a);
        assert(table_frame(a,b));restore_frame(model,tokens.drop_last(),b);
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(20)]
pub proof fn restore_related<V>(eq:spec_fn(Port,V,V)->bool,model:s::Model<V>,a:s::State<V>,b:s::State<V>,left:Seq<nat>,right:Seq<nat>)
    requires table_primitives(model),p::well_formed(a),p::well_formed(b),related(eq,model,a,b),accumulators_related(eq,model,left,right),
    ensures related(eq,model,s::restore(model,left,a),s::restore(model,right,b)),
        p::well_formed(s::restore(model,left,a)),p::well_formed(s::restore(model,right,b)),
{
    restore_frame(model,left,a);restore_frame(model,right,b);
    let obs=|u:s::State<V>,v:s::State<V>|observed(eq,u,v);
    assert(obs(accumulator(model,left)(a),accumulator(model,right)(b)));
    frames_related(eq,model,a,b,s::restore(model,left,a),s::restore(model,right,b));
}

pub proof fn guard_observations<V>(eq:spec_fn(Port,V,V)->bool,model:s::Model<V>,a:s::State<V>,b:s::State<V>,n:usize,view:ISet<Binding>)
    requires p::well_formed(a),p::well_formed(b),related(eq,model,a,b),
    ensures s::target(a,n,view)==s::target(b,n,view),s::coherent(a,n)==s::coherent(b,n),
        s::registered(a,n) ==> a.tables[n].dom()==b.tables[n].dom(),
{
    rows::projection_to_tables(eq,a,b);
    assert forall|key:Port,owner:usize| s::publishes(a,key,owner)==s::publishes(b,key,owner) by {
        if s::registered(a,owner) {assert(a.tables[owner].dom()==b.tables[owner].dom());}
    }
}

pub proof fn edit_related<V>(eq:spec_fn(Port,V,V)->bool,model:s::Model<V>,a:s::State<V>,b:s::State<V>,n:usize,
    phase:Phase,view:ISet<Binding>,left:Option<nat>,right:Option<nat>,acc_left:Seq<nat>,acc_right:Seq<nat>)
    requires p::well_formed(a),p::well_formed(b),s::registered(a,n),related(eq,model,a,b),
        continuations(eq,model,n,left,right),accumulators_related(eq,model,acc_left,acc_right),
    ensures related(eq,model,s::edit(a,n,phase,view,left,acc_left),s::edit(b,n,phase,view,right,acc_right)),
{
    projection::unique_owner(a);projection::unique_owner(b);
    projection::lifecycle_edit(a,n,phase,view,left,acc_left,ISet::full());
    projection::lifecycle_edit(b,n,phase,view,right,acc_right,ISet::full());
    assert forall|k:usize| s::registered(s::edit(a,n,phase,view,left,acc_left),k) implies {
        &&& iterator_related(eq,model,k,s::edit(a,n,phase,view,left,acc_left).effects[k],s::edit(b,n,phase,view,right,acc_right).effects[k])
        &&& continuations(eq,model,k,s::edit(a,n,phase,view,left,acc_left).iterators[k],s::edit(b,n,phase,view,right,acc_right).iterators[k])
        &&& accumulators_related(eq,model,s::edit(a,n,phase,view,left,acc_left).accumulators[k],s::edit(b,n,phase,view,right,acc_right).accumulators[k])
    } by {assert(s::registered(a,k));if k!=n {}}
}

pub open spec fn successor<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,b:s::State<V>,n:usize,rule:r::Rule,new_effect:nat)->s::State<V> {
    match rule {
        r::Rule::Insert=>s::State {control:z.control,tables:b.tables.insert(n,IMap::empty()),effects:b.effects.insert(n,new_effect),
            iterators:b.iterators.insert(n,None),accumulators:b.accumulators.insert(n,Seq::empty())},
        r::Rule::Retire=>s::State {control:z.control,..b},
        r::Rule::Remove=>s::erase(b,n),
        r::Rule::Begin=>s::edit(b,n,Phase::Loading,z.control.fibers[n].committed,Some(b.effects[n]),Seq::empty()),
        r::Rule::Iter | r::Rule::Finish=>{
            let y=(model.iterate)(n,b.iterators[n].unwrap(),b);
            s::edit(y.state,n,if rule==r::Rule::Iter {Phase::Loading} else {Phase::Active},b.control.fibers[n].committed,
                if rule==r::Rule::Iter {y.next} else {None},b.accumulators[n].push(y.inverse))
        },
        r::Rule::Divert=>{
            if z==s::edit(a,n,Phase::Unloading,a.control.fibers[n].committed,None,a.accumulators[n]) {
                s::edit(b,n,Phase::Unloading,b.control.fibers[n].committed,None,b.accumulators[n])
            } else {let y=(model.iterate)(n,b.iterators[n].unwrap(),b);
                s::edit(y.state,n,Phase::Unloading,b.control.fibers[n].committed,None,b.accumulators[n].push(y.inverse))}
        },
        r::Rule::Leave=>s::edit(b,n,Phase::Unloading,b.control.fibers[n].committed,None,b.accumulators[n]),
        r::Rule::Unload=>s::edit(s::restore(model,b.accumulators[n],b),n,Phase::Inactive,ISet::empty(),None,Seq::empty()),
        _=>b,
    }
}

/// Function fields of a fresh row are discharged independently of the table
/// observation and structural preservation obligations.
#[verifier::spinoff_prover]
proof fn inserted_fields_related<V>(eq:spec_fn(Port,V,V)->bool,model:s::Model<V>,a:s::State<V>,z:s::State<V>,b:s::State<V>,y:s::State<V>,n:usize)
    requires related(eq,model,a,b),p::insert_map(a,z,n),p::insert_map(b,y,n),z.control==y.control,
        iterator_related(eq,model,n,z.effects[n],y.effects[n]),observed(eq,z,y),
    ensures related(eq,model,z,y),
{
    empty_accumulators(eq,model);
    assert forall|k:usize| s::registered(z,k) implies {
        &&& iterator_related(eq,model,k,z.effects[k],y.effects[k])
        &&& continuations(eq,model,k,z.iterators[k],y.iterators[k])
        &&& accumulators_related(eq,model,z.accumulators[k],y.accumulators[k])
    } by {if k!=n {assert(s::registered(a,k));}}
}

#[verifier::spinoff_prover]
pub proof fn insert_simulates<V>(eq:spec_fn(Port,V,V)->bool,model:s::Model<V>,a:s::State<V>,z:s::State<V>,b:s::State<V>,n:usize,new_effect:nat)
    requires p::well_formed(a),p::well_formed(b),related(eq,model,a,b),s::step(model,a,z,n,r::Rule::Insert),
        iterator_related(eq,model,n,z.effects[n],new_effect),
    ensures s::step(model,b,successor(model,a,z,b,n,r::Rule::Insert,new_effect),n,r::Rule::Insert),
        related(eq,model,z,successor(model,a,z,b,n,r::Rule::Insert,new_effect)),
        p::well_formed(successor(model,a,z,b,n,r::Rule::Insert,new_effect)),
{
    crate::rule_frames::factorization(model,a,z,n,r::Rule::Insert);
    assert(p::insert_map(a,z,n));
    let y=successor(model,a,z,b,n,r::Rule::Insert,new_effect);
    assert(p::insert_map(b,y,n));p::insert_preservation(b,y,n);
    projection::empty_insertion(a,z,n,ISet::full());projection::empty_insertion(b,y,n,ISet::full());
    empty_accumulators(eq,model);
    inserted_fields_related(eq,model,a,z,b,y,n);
}

pub proof fn same_tables_projection<V>(a:s::State<V>,b:s::State<V>)
    requires p::well_formed(a),p::well_formed(b),a.control.fibers.dom()==b.control.fibers.dom(),a.tables==b.tables,
    ensures projection::project(a,ISet::full())==projection::project(b,ISet::full()),
{
    projection::unique_owner(a);projection::unique_owner(b);
    assert(projection::bindings_equal(a,b));projection::projection_equal(a,b,ISet::full());
}

/// A constructive nine-rule simulation. Insert payloads may carry different
/// but bisimilar roots. Existing function fields and all journal lengths may
/// differ. The source endpoint is well formed; no target step or target endpoint
/// relation is assumed. Table-only primitives are the explicit scope boundary.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn step_simulates<V>(eq:spec_fn(Port,V,V)->bool,model:s::Model<V>,a:s::State<V>,z:s::State<V>,b:s::State<V>,n:usize,rule:r::Rule,new_effect:nat)
    requires table_primitives(model),p::well_formed(a),p::well_formed(z),p::well_formed(b),related(eq,model,a,b),
        s::step(model,a,z,n,rule),rule==r::Rule::Insert ==> iterator_related(eq,model,n,z.effects[n],new_effect),
    ensures s::step(model,b,successor(model,a,z,b,n,rule,new_effect),n,rule),
        related(eq,model,z,successor(model,a,z,b,n,rule,new_effect)),
        p::well_formed(successor(model,a,z,b,n,rule,new_effect)),
{
    let y=successor(model,a,z,b,n,rule,new_effect);
    guard_observations(eq,model,a,b,n,z.control.fibers[n].committed);
    empty_accumulators(eq,model);
    match rule {
        r::Rule::Insert=>{insert_simulates(eq,model,a,z,b,n,new_effect);},
        r::Rule::Retire=>{
            assert(s::shaped(y)) by {
                assert forall|k:usize| s::registered(y,k) implies {
                    &&& y.tables[k].dom().subset_of(y.control.fibers[k].provisions)
                    &&& (y.control.fibers[k].phase==Phase::Inactive ==> y.iterators[k].is_none() && y.accumulators[k].len()==0 && y.control.fibers[k].committed.is_empty())
                    &&& (y.control.fibers[k].phase==Phase::Loading ==> y.iterators[k].is_some())
                    &&& (y.control.fibers[k].phase==Phase::Active || y.control.fibers[k].phase==Phase::Unloading ==> y.iterators[k].is_none())
                } by {assert(s::registered(a,k));assert(s::registered(b,k));if k!=n {assert(a.control.fibers[k]==z.control.fibers[k]);}}
            }
            assert(p::well_formed(y));same_tables_projection(a,z);same_tables_projection(b,y);
            assert forall|k:usize| s::registered(z,k) implies {
                &&& iterator_related(eq,model,k,z.effects[k],y.effects[k])
                &&& continuations(eq,model,k,z.iterators[k],y.iterators[k])
                &&& accumulators_related(eq,model,z.accumulators[k],y.accumulators[k])
            } by {assert(s::registered(a,k));}
        },
        r::Rule::Remove=>{
            crate::rule_frames::factorization(model,a,z,n,rule);assert(z==s::erase(a,n));
            assert(a.tables[n].dom()==b.tables[n].dom());assert(b.tables[n].is_empty());
            crate::deletion::erase_shaped(b,n);assert(p::well_formed(y));
            projection::unique_owner(a);projection::unique_owner(b);
            projection::empty_erasure(a,n,ISet::full());projection::empty_erasure(b,n,ISet::full());
            assert forall|k:usize| s::registered(z,k) implies {
                &&& iterator_related(eq,model,k,z.effects[k],y.effects[k])
                &&& continuations(eq,model,k,z.iterators[k],y.iterators[k])
                &&& accumulators_related(eq,model,z.accumulators[k],y.accumulators[k])
            } by {assert(s::registered(a,k));assert(k!=n);}
        },
        r::Rule::Begin=>{
            assert(iterator_related(eq,model,n,a.effects[n],b.effects[n]));
            edit_related(eq,model,a,b,n,Phase::Loading,z.control.fibers[n].committed,Some(a.effects[n]),Some(b.effects[n]),Seq::empty(),Seq::empty());
            p::shaped_edit(b,n,Phase::Loading,z.control.fibers[n].committed,Some(b.effects[n]),Seq::empty());
        },
        r::Rule::Iter | r::Rule::Finish | r::Rule::Divert=>{
            if rule==r::Rule::Divert && z==s::edit(a,n,Phase::Unloading,a.control.fibers[n].committed,None,a.accumulators[n]) {
                edit_related(eq,model,a,b,n,Phase::Unloading,a.control.fibers[n].committed,None,None,a.accumulators[n],b.accumulators[n]);
                p::shaped_edit(b,n,Phase::Unloading,b.control.fibers[n].committed,None,b.accumulators[n]);
            } else {
                let i=a.iterators[n].unwrap();let j=b.iterators[n].unwrap();
                assert(continuations(eq,model,n,a.iterators[n],b.iterators[n]));
                assert(iterator_related(eq,model,n,i,j));assert(b.iterators[n].is_some());
                let x=(model.iterate)(n,i,a);let v=(model.iterate)(n,j,b);
                call_related(eq,model,n,i,j,a,b);
                assert(table_frame(a,x.state));assert(table_frame(b,v.state));
                frames_related(eq,model,a,b,x.state,v.state);
                append_inverse(eq,model,a.accumulators[n],b.accumulators[n],x.inverse,v.inverse);
                let phase=if rule==r::Rule::Iter {Phase::Loading} else if rule==r::Rule::Finish {Phase::Active} else {Phase::Unloading};
                let next_left=if rule==r::Rule::Iter {x.next} else {None};
                let next_right=if rule==r::Rule::Iter {v.next} else {None};
                edit_related(eq,model,x.state,v.state,n,phase,a.control.fibers[n].committed,next_left,next_right,
                    a.accumulators[n].push(x.inverse),b.accumulators[n].push(v.inverse));
                p::shaped_edit(v.state,n,phase,b.control.fibers[n].committed,next_right,b.accumulators[n].push(v.inverse));
            }
        },
        r::Rule::Leave=>{
            edit_related(eq,model,a,b,n,Phase::Unloading,a.control.fibers[n].committed,None,None,a.accumulators[n],b.accumulators[n]);
            p::shaped_edit(b,n,Phase::Unloading,b.control.fibers[n].committed,None,b.accumulators[n]);
        },
        r::Rule::Unload=>{
            restore_related(eq,model,a,b,a.accumulators[n],b.accumulators[n]);
            let x=s::restore(model,a.accumulators[n],a);let v=s::restore(model,b.accumulators[n],b);
            restore_frame(model,a.accumulators[n],a);restore_frame(model,b.accumulators[n],b);
            edit_related(eq,model,x,v,n,Phase::Inactive,ISet::empty(),None,None,Seq::empty(),Seq::empty());
            p::shaped_edit(v,n,Phase::Inactive,ISet::empty(),None,Seq::empty());
        },
        _=>{},
    }
}

/// The full function-field relation is a PER; arbitrary code is not silently
/// assumed to respect observations merely because its identifier is unchanged.
#[verifier::spinoff_prover]
pub proof fn relation_partial_equivalence<V>(eq:spec_fn(Port,V,V)->bool,model:s::Model<V>,a:s::State<V>,b:s::State<V>,c:s::State<V>)
    requires forall|key:Port| #[trigger] q::key_equivalent(eq,key),related(eq,model,a,b),
    ensures related(eq,model,b,a),related(eq,model,a,a),related(eq,model,b,b),
        related(eq,model,b,c) ==> related(eq,model,a,c),
{
    observation_equivalence(eq);let obs=|x:s::State<V>,y:s::State<V>|observed(eq,x,y);
    assert(obs(a,b));assert(obs(b,a));assert(obs(a,a));assert(obs(b,b));
    if related(eq,model,b,c) {assert(obs(b,c));assert(obs(a,c));}
    assert forall|n:usize| s::registered(a,n) implies {
        &&& iterator_related(eq,model,n,b.effects[n],a.effects[n])
        &&& iterator_related(eq,model,n,a.effects[n],a.effects[n])
        &&& iterator_related(eq,model,n,b.effects[n],b.effects[n])
        &&& continuations(eq,model,n,b.iterators[n],a.iterators[n])
        &&& continuations(eq,model,n,a.iterators[n],a.iterators[n])
        &&& continuations(eq,model,n,b.iterators[n],b.iterators[n])
        &&& accumulators_related(eq,model,b.accumulators[n],a.accumulators[n])
        &&& accumulators_related(eq,model,a.accumulators[n],a.accumulators[n])
        &&& accumulators_related(eq,model,b.accumulators[n],b.accumulators[n])
        &&& (related(eq,model,b,c) ==> iterator_related(eq,model,n,a.effects[n],c.effects[n])
            && continuations(eq,model,n,a.iterators[n],c.iterators[n])
            && accumulators_related(eq,model,a.accumulators[n],c.accumulators[n]))
    } by {
        assert(iterator_related(eq,model,n,a.effects[n],b.effects[n]));
        assert(continuations(eq,model,n,a.iterators[n],b.iterators[n]));
        assert(accumulators_related(eq,model,a.accumulators[n],b.accumulators[n]));
        if related(eq,model,b,c) {
            assert(s::registered(b,n));
            assert(iterator_related(eq,model,n,b.effects[n],c.effects[n]));
            assert(continuations(eq,model,n,b.iterators[n],c.iterators[n]));
            assert(accumulators_related(eq,model,b.accumulators[n],c.accumulators[n]));
        }
        q::iterator_partial_equivalence(obs,family(model,n),a.effects[n],b.effects[n],c.effects[n]);
        q::iterator_partial_equivalence(obs,family(model,n),a.iterators[n].unwrap(),b.iterators[n].unwrap(),c.iterators[n].unwrap());
        o::map_partial_equivalence(obs,accumulator(model,a.accumulators[n]),accumulator(model,b.accumulators[n]),accumulator(model,c.accumulators[n]));
        if a.iterators[n].is_some() {assert(b.iterators[n].is_some());}
    }
    assert forall|n:usize| s::registered(b,n) implies {
        &&& iterator_related(eq,model,n,b.effects[n],a.effects[n])
        &&& continuations(eq,model,n,b.iterators[n],a.iterators[n])
        &&& accumulators_related(eq,model,b.accumulators[n],a.accumulators[n])
    } by {assert(s::registered(a,n));}
    assert forall|n:usize| s::registered(b,n) implies {
        &&& iterator_related(eq,model,n,b.effects[n],b.effects[n])
        &&& continuations(eq,model,n,b.iterators[n],b.iterators[n])
        &&& accumulators_related(eq,model,b.accumulators[n],b.accumulators[n])
    } by {assert(s::registered(a,n));}
}

pub open spec fn replay<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>,roots:Seq<nat>,initial:s::State<V>)->Seq<s::State<V>>
    decreases labels.len(),
{
    if labels.len()==0 {seq![initial]}
    else {
        let previous=replay(model,states.drop_last(),labels.drop_last(),roots.drop_last(),initial);
        previous.push(successor(model,states[states.len()-2],states.last(),previous.last(),labels.last().0,labels.last().1,roots.last()))
    }
}

/// Construct every target state from the original legal trace and field-level
/// root correspondences. No target execution is supplied as a premise.
#[verifier::spinoff_prover]
#[verifier::rlimit(20)]
pub proof fn execution_simulates<V>(eq:spec_fn(Port,V,V)->bool,model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>,roots:Seq<nat>,initial:s::State<V>)
    requires table_primitives(model),s::execution(model,states,labels),roots.len()==labels.len(),
        p::well_formed(initial),related(eq,model,states.first(),initial),
        forall|i:int| 0<=i<states.len() ==> p::well_formed(states[i]),
        forall|i:int| 0<=i<labels.len() && labels[i].1==r::Rule::Insert ==>
            iterator_related(eq,model,labels[i].0,states[i+1].effects[labels[i].0],roots[i]),
    ensures {
        let target=replay(model,states,labels,roots,initial);
        &&& target.len()==states.len() && target.first()==initial && s::execution(model,target,labels)
        &&& forall|i:int| 0<=i<states.len() ==> related(eq,model,states[i],target[i]) && p::well_formed(target[i])
    },
    decreases labels.len(),
{
    if labels.len()>0 {
        let shorter=states.drop_last();let steps=labels.drop_last();let code=roots.drop_last();
        execution_simulates(eq,model,shorter,steps,code,initial);
        let previous=replay(model,shorter,steps,code,initial);let last=(labels.len()-1) as int;
        assert(states[last]==shorter.last());assert(previous.last()==previous[last]);
        step_simulates(eq,model,states[last],states[last+1],previous.last(),labels[last].0,labels[last].1,roots[last]);
        let target=replay(model,states,labels,roots,initial);
        assert forall|i:int| 0<=i<labels.len() implies s::step(model,target[i],target[i+1],labels[i].0,labels[i].1) by {
            if i<last {assert(s::step(model,previous[i],previous[i+1],steps[i].0,steps[i].1));}
        }
        assert forall|i:int| 0<=i<states.len() implies related(eq,model,states[i],target[i]) && p::well_formed(target[i]) by {
            if i<states.len()-1 {assert(shorter[i]==states[i]);assert(previous[i]==target[i]);}
        }
    } else {assert(states.len()==1);assert(states.first()==states[0]);}
}

/// Two distinct code paths (0 -> 1 and 10 -> 11) with distinct actual inverse
/// identifiers. Their recursive behavior, not identifier equality, agrees.
pub open spec fn alias_model<V>()->s::Model<V> {
    s::Model {iterate:|_:usize,id:nat,a:s::State<V>|s::Yield {state:a,inverse:id+100,
        next:if id==0 {Some(1)} else if id==10 {Some(11)} else {None}},
        undo:|_:nat,a:s::State<V>|a}
}
pub open spec fn pending(id:nat)->bool {id==0 || id==10}

pub proof fn alias_iterators<V>(eq:spec_fn(Port,V,V)->bool,actor:usize,left:nat,right:nat)
    requires pending(left)==pending(right),
    ensures iterator_related(eq,alias_model::<V>(),actor,left,right),table_primitives(alias_model::<V>()),
{
    let obs=|a:s::State<V>,b:s::State<V>|observed(eq,a,b);let f=family(alias_model::<V>(),actor);
    let relation=|i:nat,j:nat|pending(i)==pending(j);
    assert(q::bisimulation(obs,f,relation)) by {
        assert forall|i:nat,j:nat,a:s::State<V>,b:s::State<V>| #![trigger f(i,a),f(j,b)] relation(i,j) && obs(a,b) implies {
            &&& obs(f(i,a).state,f(j,b).state)
            &&& o::related_maps(obs,f(i,a).undo,f(j,b).undo)
            &&& q::continuation(relation,f(i,a).next,f(j,b).next)
        } by {if pending(i) {if i==0 {} else {assert(i==10);}if j==0 {} else {assert(j==10);}}}
    }
    assert(q::iterator_related(obs,f,left,right));
}

pub proof fn alias_restore<V>(tokens:Seq<nat>,a:s::State<V>)
    ensures s::restore(alias_model::<V>(),tokens,a)==a,
    decreases tokens.len(),
{if tokens.len()>0 {alias_restore(tokens.drop_last(),a);}}

/// Unequal lengths are genuinely accepted, not hidden by a pointwise token
/// relation. This supplies, for example, an empty and a two-token identity word.
pub proof fn alias_accumulators<V>(eq:spec_fn(Port,V,V)->bool,left:Seq<nat>,right:Seq<nat>)
    ensures accumulators_related(eq,alias_model::<V>(),left,right),
{
    assert forall|a:s::State<V>,b:s::State<V>| observed(eq,a,b) implies
        #[trigger] observed(eq,s::restore(alias_model::<V>(),left,a),s::restore(alias_model::<V>(),right,b)) by {
        alias_restore(left,a);alias_restore(right,b);
    }
}

#[verifier::opaque]
pub open spec fn example_trace()->Seq<s::State<int>> {
    let a0=s::empty_state::<int>();
    let a1=s::extend_child(a0,crate::global::insert_fiber(a0.control,0,None,ISet::empty(),ISet::empty()),0,0);
    let a2=s::edit(a1,0,Phase::Loading,ISet::empty(),Some(0),Seq::empty());
    let a3=s::edit(a2,0,Phase::Loading,ISet::empty(),Some(1),seq![100nat]);
    let a4=s::edit(a3,0,Phase::Active,ISet::empty(),None,seq![100nat,101nat]);
    let a5=s::with_control(a4,crate::global::retire_fiber(a4.control,0));
    let a6=s::edit(a5,0,Phase::Unloading,ISet::empty(),None,seq![100nat,101nat]);
    let a7=s::edit(a6,0,Phase::Inactive,ISet::empty(),None,Seq::empty());
    seq![a0,a1,a2,a3,a4,a5,a6,a7]
}
pub open spec fn example_labels()->Seq<(usize,r::Rule)> {
    seq![(0usize,r::Rule::Insert),(0usize,r::Rule::Begin),(0usize,r::Rule::Iter),(0usize,r::Rule::Finish),
        (0usize,r::Rule::Retire),(0usize,r::Rule::Leave),(0usize,r::Rule::Unload)]
}
pub open spec fn example_roots()->Seq<nat> {seq![10nat,0,0,0,0,0,0]}
pub open spec fn example_target()->Seq<s::State<int>> {
    replay(alias_model::<int>(),example_trace(),example_labels(),example_roots(),s::empty_state::<int>())
}

/// Actual executions from empty: Begin/Iter use different code identities and
/// Finish stores different inverse tokens, then real Unload consumes each side's
/// own stack. The old literal-token relation rejects these related states.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn nonliteral_execution()
    ensures s::execution(alias_model::<int>(),example_trace(),example_labels()),
        s::execution(alias_model::<int>(),example_target(),example_labels()),
        example_trace().first()==s::empty_state::<int>() && example_target().first()==s::empty_state::<int>(),
        forall|i:int| 0<=i<8 ==> related(crate::recovery_examples::equality(),alias_model::<int>(),example_trace()[i],example_target()[i])
            && p::well_formed(example_trace()[i]) && p::well_formed(example_target()[i]),
        example_trace()[2].effects[0usize]==0 && example_target()[2].effects[0usize]==10,
        example_trace()[3].iterators[0usize]==Some(1nat) && example_target()[3].iterators[0usize]==Some(11nat),
        example_trace()[4].accumulators[0usize]==seq![100nat,101nat] && example_target()[4].accumulators[0usize]==seq![110nat,111nat],
        !q::related(crate::recovery_examples::equality(),example_trace()[3],example_target()[3]),
        accumulators_related(crate::recovery_examples::equality(),alias_model::<int>(),Seq::empty(),seq![123nat,456nat]),
{
    reveal(example_trace);let states=example_trace();let labels=example_labels();let model=alias_model::<int>();
    let eq=crate::recovery_examples::equality();
    p::empty_well_formed::<int>();
    assert(p::insert_map(states[0],states[1],0));p::insert_preservation(states[0],states[1],0);
    assert(s::step(model,states[0],states[1],0,r::Rule::Insert));
    assert(s::step(model,states[1],states[2],0,r::Rule::Begin));p::begin_preservation(states[1],states[2],0);
    assert(p::table_map(states[2],states[2],0));assert(s::step(model,states[2],states[3],0,r::Rule::Iter));
    p::full_preservation(model,states[2],states[3],0,r::Rule::Iter);
    assert(seq![100nat].push(101nat) =~= seq![100nat,101nat]);
    assert(p::table_map(states[3],states[3],0));assert(s::step(model,states[3],states[4],0,r::Rule::Finish));
    p::full_preservation(model,states[3],states[4],0,r::Rule::Finish);
    assert(s::step(model,states[4],states[5],0,r::Rule::Retire));p::retire_preservation(states[4],states[5],0);
    assert(s::step(model,states[5],states[6],0,r::Rule::Leave));p::full_preservation(model,states[5],states[6],0,r::Rule::Leave);
    assert(p::table_map(states[6],states[6],0));
    alias_restore(seq![100nat,101nat],states[6]);
    assert(s::step(model,states[6],states[7],0,r::Rule::Unload));
    reveal_with_fuel(p::admissible_restore,3);
    assert(p::admissible_restore(model,seq![100nat,101nat],states[6],0));
    assert forall|i:int| 0<=i<labels.len() implies s::step(model,states[i],states[i+1],labels[i].0,labels[i].1)
        && p::admissible_step(model,states[i],states[i+1],labels[i].0,labels[i].1) by {
        if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {} else {
            assert(i==6);alias_restore(seq![100nat,101nat],states[6]);
        }
    }
    p::execution_preservation(model,states,labels);
    alias_iterators(eq,0,0,10);alias_accumulators(eq,Seq::empty(),seq![123nat,456nat]);
    assert(related(eq,model,states.first(),s::empty_state::<int>()));
    execution_simulates(eq,model,states,labels,example_roots(),s::empty_state::<int>());
    reveal_with_fuel(replay,8);
}
}
