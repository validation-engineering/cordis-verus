//! The paper's registry clauses and component-level provision totality.
//!
//! Definition 63 is separated from the stronger reachable-state invariant.
//! Definition 76 quantifies all completed runs, not just one state's Active
//! entries. The generic iterator predicate and the operational specialization
//! are distinct: arbitrary interleavings require a representation/independence
//! bridge, which is not supplied by a current-state domain check.
#[cfg(verus_keep_ghost)]
use crate::{
    foundations as f, global, iterators as it, lifecycle_ordering as life,
    orchestration_support_cycle as unit_example, preservation as inv, quotient as q,
    recovery_examples as ex, refinement as r, rule_frames, semantics as s, Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {

/// The graph encoding of omega : dependencies -> registered names. Function
/// typing supplies exact domain and uniqueness, without requiring the named
/// provider to declare this key or requiring it to differ from its consumer.
pub open spec fn committed_view(a:r::State,n:usize)->bool {
    &&& forall|b:Binding| a.fibers[n].committed.contains(b) ==>
        a.fibers[n].dependencies.contains(Port {key:b.key,realm:b.realm}) && r::registered(a,b.provider)
    &&& forall|k:Port| a.fibers[n].dependencies.contains(k) ==> exists|b:Binding|
        a.fibers[n].committed.contains(b) && b.key==k.key && b.realm==k.realm
    &&& forall|x:Binding,y:Binding| a.fibers[n].committed.contains(x) && a.fibers[n].committed.contains(y)
        && x.key==y.key && x.realm==y.realm ==> x.provider==y.provider
}

/// Exactly the four clauses of Definition 63, on the graph representation.
/// Finite registry/tree shape belongs to Definition 50, and can be supplied
/// separately. No allocation order or no-self-dependency condition is added.
pub open spec fn registry(a:r::State)->bool {
    &&& forall|n:usize| r::registered(a,n) ==> match a.fibers[n].parent {None=>true,Some(parent)=>r::registered(a,parent)}
    &&& forall|n:usize,m:usize,k:Port| r::registered(a,n) && r::registered(a,m) && n!=m
        ==> !(a.fibers[n].provisions.contains(k) && a.fibers[m].provisions.contains(k))
    &&& forall|n:usize| r::registered(a,n) && a.fibers[n].phase!=Phase::Inactive ==> committed_view(a,n)
    &&& forall|n:usize,b:Binding| r::registered(a,n) && a.fibers[n].phase!=Phase::Inactive
        && a.fibers[n].dependencies.contains(Port {key:b.key,realm:b.realm}) && a.fibers[n].committed.contains(b)
        ==> r::registered(a,b.provider) && a.fibers[b.provider].phase!=Phase::Inactive
}

pub proof fn strengthened_implies_paper<V>(a:s::State<V>)
    requires inv::well_formed(a),
    ensures registry(a.control),
{ }

/// A finite one-node tree with a total installed self-view satisfies all four
/// printed clauses. It is not claimed reachable from empty: Begin cannot
/// bootstrap this self-provider. Reachability is a separate stronger property.
pub open spec fn self_view()->s::State<int> {
    s::State {
        control:r::State {fibers:IMap::empty().insert(0usize,r::Fiber {parent:None,retired:false,phase:Phase::Active,
            dependencies:ex::provided(0),provisions:ex::provided(0),
            committed:ISet::empty().insert(Binding {key:0,realm:0,provider:0})})},
        tables:IMap::empty().insert(0usize,IMap::empty().insert(ex::key(0),7int)),
        effects:IMap::empty().insert(0usize,0nat),iterators:IMap::empty().insert(0usize,None),
        accumulators:IMap::empty().insert(0usize,Seq::empty()),
    }
}
pub proof fn paper_does_not_imply_strengthened()
    ensures registry(self_view().control),s::shaped(self_view()),inv::structural(self_view().control),
        !inv::well_formed(self_view()),
{
    let a=self_view();let rank=|_:usize|0nat;
    assert(r::name_bound(a.control,1));assert(r::parent_ranking(a.control,rank));
    assert(a.control.fibers[0usize].committed.contains(Binding {key:0,realm:0,provider:0}));
    if inv::well_formed(a) {assert(0usize!=0usize);}
}

/// Component-level total provision: for every dependency-satisfying context
/// and every completed finite run of this root, all declared provisions were
/// installed. Component typing separately bounds the output domain, yielding
/// the equality in Definition 76. This is conditional on completion, so the
/// definition itself does not assert termination or witnessed membership.
pub open spec fn completion_total<S,I,K,V>(family:q::IteratorFamily<S,I>,root:I,
    dependencies:ISet<K>,provisions:ISet<K>,coeffects:spec_fn(S)->IMap<K,V>,owned:spec_fn(S)->IMap<K,V>)->bool {
    forall|input:S,fuel:nat| dependencies.subset_of(coeffects(input).dom())
        && (#[trigger] it::run(family,Some(root),fuel,f::unit(input))).next.is_none()
        ==> provisions.subset_of(owned(it::run(family,Some(root),fuel,f::unit(input)).current.value).dom())
}

pub proof fn completed_provision_domain<S,I,K,V>(family:q::IteratorFamily<S,I>,root:I,
    dependencies:ISet<K>,provisions:ISet<K>,coeffects:spec_fn(S)->IMap<K,V>,owned:spec_fn(S)->IMap<K,V>,input:S,fuel:nat)
    requires completion_total(family,root,dependencies,provisions,coeffects,owned),dependencies.subset_of(coeffects(input).dom()),
        it::run(family,Some(root),fuel,f::unit(input)).next.is_none(),
        owned(it::run(family,Some(root),fuel,f::unit(input)).current.value).dom().subset_of(provisions),
    ensures owned(it::run(family,Some(root),fuel,f::unit(input)).current.value).dom()==provisions,
{
    assert(owned(it::run(family,Some(root),fuel,f::unit(input)).current.value).dom() =~= provisions);
}

/// A real Begin...Finish activation of a fixed component. Any number of
/// foreign steps may interleave while the actor remains Loading. No full-table
/// requirement is hidden in this predicate or in the Finish rule.
pub open spec fn activation<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>,actor:usize,
    effect:nat,dependencies:ISet<Port>,provisions:ISet<Port>)->bool {
    &&& labels.len()>=2 && inv::execution(model,states,labels) && inv::well_formed(states.first())
    &&& labels.first()==(actor,r::Rule::Begin) && labels.last()==(actor,r::Rule::Finish)
    &&& s::registered(states.first(),actor) && states.first().effects[actor]==effect
    &&& states.first().control.fibers[actor].dependencies==dependencies && states.first().control.fibers[actor].provisions==provisions
    &&& forall|i:int| 1<=i<labels.len() ==> s::registered(states[i],actor) && states[i].control.fibers[actor].phase==Phase::Loading
}

/// Operational specialization, quantified over all successful activations of
/// this effect and interface rather than over the Active entries of one state.
pub open spec fn operational_total<V>(model:s::Model<V>,effect:nat,dependencies:ISet<Port>,provisions:ISet<Port>)->bool {
    forall|states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>,actor:usize|
        #[trigger] activation(model,states,labels,actor,effect,dependencies,provisions)
        ==> provisions.subset_of(states.last().tables[actor].dom())
}

pub proof fn activation_endpoint<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>,actor:usize,
    effect:nat,dependencies:ISet<Port>,provisions:ISet<Port>)
    requires activation(model,states,labels,actor,effect,dependencies,provisions),
    ensures inv::well_formed(states.last()),s::registered(states.last(),actor),states.last().control.fibers[actor].phase==Phase::Active,
        states.last().effects[actor]==effect,states.last().control.fibers[actor].dependencies==dependencies,
        states.last().control.fibers[actor].provisions==provisions,
{
    let i=labels.len()-1;assert(s::step(model,states[i],states.last(),actor,r::Rule::Finish));
    inv::execution_preservation(model,states,labels);
    assert(s::registered(states.last(),actor));
    assert forall|j:int| 0<=j<states.len() implies s::registered(states[j],actor) by {
        if j==0 {} else if j==states.len()-1 {} else {assert(1<=j<labels.len());}
    }
    rule_frames::metadata_lifetime(model,states,labels,actor,0,states.len()-1);
}

pub proof fn actual_finish_total<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>,actor:usize,
    effect:nat,dependencies:ISet<Port>,provisions:ISet<Port>)
    requires operational_total(model,effect,dependencies,provisions),activation(model,states,labels,actor,effect,dependencies,provisions),
    ensures states.last().tables[actor].dom()==provisions,states.last().control.fibers[actor].phase==Phase::Active,
{
    activation_endpoint(model,states,labels,actor,effect,dependencies,provisions);
    assert(states.last().tables[actor].dom() =~= provisions);
}

/// After a completed activation, an actor remaining Active cannot install or
/// remove bindings. Foreign transitions preserve this table's domain by the
/// actual local confinement rules, even if its values change.
pub proof fn active_domain_constant<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>,actor:usize)
    requires life::trace(model,states,labels),
        forall|i:int| 0<=i<states.len() ==> s::registered(states[i],actor) && states[i].control.fibers[actor].phase==Phase::Active,
    ensures states.last().tables[actor].dom()==states.first().tables[actor].dom(),
    decreases labels.len(),
{
    if labels.len()>0 {
        let prefix=states.drop_last();let steps=labels.drop_last();
        assert(life::trace(model,prefix,steps)) by {
            assert forall|i:int| 0<=i<steps.len() implies s::step(model,prefix[i],prefix[i+1],steps[i].0,steps[i].1)
                && inv::admissible_step(model,prefix[i],prefix[i+1],steps[i].0,steps[i].1) by {}
        }
        active_domain_constant(model,prefix,steps,actor);inv::execution_preservation(model,states,labels);
        let a=prefix.last();let z=states.last();let (who,rule)=labels.last();
        assert(s::step(model,a,z,who,rule));
        if who==actor {assert(rule==r::Rule::Retire);assert(a.tables==z.tables);}
        else {life::foreign_table_step(model,a,z,who,rule,actor);}
    }
}

pub proof fn completed_active_total<V>(model:s::Model<V>,activation_states:Seq<s::State<V>>,activation_labels:Seq<(usize,r::Rule)>,
    suffix:Seq<s::State<V>>,suffix_labels:Seq<(usize,r::Rule)>,actor:usize,effect:nat,dependencies:ISet<Port>,provisions:ISet<Port>)
    requires operational_total(model,effect,dependencies,provisions),
        activation(model,activation_states,activation_labels,actor,effect,dependencies,provisions),
        life::trace(model,suffix,suffix_labels),suffix.first()==activation_states.last(),
        forall|i:int| 0<=i<suffix.len() ==> s::registered(suffix[i],actor) && suffix[i].control.fibers[actor].phase==Phase::Active,
    ensures suffix.last().tables[actor].dom()==provisions,
{
    actual_finish_total(model,activation_states,activation_labels,actor,effect,dependencies,provisions);
    active_domain_constant(model,suffix,suffix_labels,actor);
}

pub open spec fn unit_trace(provisions:ISet<Port>)->Seq<s::State<int>> {
    let empty=inv::empty::<int>();let start=s::extend_child(empty,global::insert_fiber(empty.control,0,None,ISet::empty(),provisions),0,0);
    let loading=s::edit(start,0,Phase::Loading,ISet::empty(),Some(0),Seq::empty());
    let active=s::edit(loading,0,Phase::Active,ISet::empty(),None,seq![0nat]);
    seq![start,loading,active]
}
pub open spec fn unit_labels()->Seq<(usize,r::Rule)> {seq![(0usize,r::Rule::Begin),(0usize,r::Rule::Finish)]}

pub proof fn actual_incomplete_unit(provisions:ISet<Port>)
    ensures activation(unit_example::unit_model(),unit_trace(provisions),unit_labels(),0,0,ISet::empty(),provisions),
        s::total_active(unit_trace(provisions).first()),unit_trace(provisions).last().tables[0usize].is_empty(),
        unit_trace(provisions).last().control.fibers[0usize].phase==Phase::Active,
{
    let states=unit_trace(provisions);let model=unit_example::unit_model();let empty=inv::empty::<int>();
    inv::empty_well_formed::<int>();assert(inv::insert_map(empty,states[0],0));inv::insert_preservation(empty,states[0],0);
    assert(s::step(model,states[0],states[1],0,r::Rule::Begin));
    assert(s::step(model,states[1],states[2],0,r::Rule::Finish));
    assert(inv::admissible_step(model,states[1],states[2],0,r::Rule::Finish));
    assert(inv::execution(model,states,unit_labels()));
}

/// Current-state total_active can be vacuous even for a component that really
/// finishes without installing its nonempty declaration. Conversely Unit with
/// empty provision satisfies both completion-level predicates universally.
pub proof fn totality_is_not_a_current_state_test()
    ensures s::total_active(unit_trace(ex::provided(0)).first()),
        !operational_total(unit_example::unit_model(),0,ISet::empty(),ex::provided(0)),
        !completion_total(unit_example::unit::<IMap<Port,int>>(),(),ISet::empty(),ex::provided(0),|a:IMap<Port,int>|a,|a:IMap<Port,int>|a),
        operational_total(unit_example::unit_model(),0,ISet::empty(),ISet::empty()),
        completion_total(unit_example::unit::<IMap<Port,int>>(),(),ISet::empty(),ISet::empty(),|a:IMap<Port,int>|a,|a:IMap<Port,int>|a),
{
    actual_incomplete_unit(ex::provided(0));
    if operational_total(unit_example::unit_model(),0,ISet::empty(),ex::provided(0)) {
        assert(ex::provided(0).subset_of(unit_trace(ex::provided(0)).last().tables[0usize].dom()));
        assert(unit_trace(ex::provided(0)).last().tables[0usize].dom().contains(ex::key(0)));
    }
    let family=unit_example::unit::<IMap<Port,int>>();let empty=IMap::<Port,int>::empty();
    reveal_with_fuel(it::run,2);
    assert(it::run(family,Some(()),1,f::unit(empty)).next.is_none());
    assert(it::run(family,Some(()),1,f::unit(empty)).current.value==empty);
    if completion_total(family,(),ISet::empty(),ex::provided(0),|a:IMap<Port,int>|a,|a:IMap<Port,int>|a) {
        assert(ex::provided(0).subset_of(empty.dom()));assert(empty.dom().contains(ex::key(0)));
    }
}
}
