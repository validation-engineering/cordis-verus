//! Strict recovery using a reverse witness for the entire pending own batch.
//!
//! New own calls contribute the inverse returned at their actual input. A
//! foreign call, including an old inverse, needs only actual source success,
//! respect, and strict commutation with the accumulated forward and undo maps.
//! It does not need a reverse witness of its own. The lifecycle guard and
//! historical receipt arguments that establish those commutations are separate
//! obligations; this module proves only the underlying partial-map algebra.
#[cfg(verus_keep_ghost)]
use crate::{
    calculus as c, foreign_unload as fu, mediated as m, observation, partial_independence as p,
    strict_journal as sj,
};
use vstd::prelude::*;

verus! {

/// The redo map witnesses the inverse of this whole batch at this one state.
/// This is a local property, not a global inverse or a per-record assertion.
pub open spec fn batch<S>(eq:spec_fn(S,S)->bool,redo:m::PartialMap<S>,
    undo:m::PartialMap<S>,state:S)->bool {
    &&& p::respects(eq,redo) && p::respects(eq,undo)
    &&& undo(state).is_some() && redo(undo(state).unwrap()).is_some()
    &&& eq(redo(undo(state).unwrap()).unwrap(),state)
}

pub proof fn empty_batch<S>(eq:spec_fn(S,S)->bool,state:S)
    requires c::equivalence(eq),
    ensures batch(eq,fu::identity(),fu::identity(),state),
{ }

/// Extending the actual journal needs no commutation between own operations.
pub proof fn own_push<S>(eq:spec_fn(S,S)->bool,redo:m::PartialMap<S>,
    undo:m::PartialMap<S>,forward:m::PartialMap<S>,inverse:m::PartialMap<S>,state:S)
    requires c::equivalence(eq),batch(eq,redo,undo,state),
        p::respects(eq,forward),p::respects(eq,inverse),
        forward(state).is_some(),inverse(forward(state).unwrap()).is_some(),
        eq(inverse(forward(state).unwrap()).unwrap(),state),
    ensures batch(eq,p::compose(forward,redo),p::compose(undo,inverse),forward(state).unwrap()),
        eq(p::compose(undo,inverse)(forward(state).unwrap()).unwrap(),undo(state).unwrap()),
{
    p::composition_respects(eq,forward,redo);p::composition_respects(eq,undo,inverse);
    let after=forward(state).unwrap();let returned=inverse(after).unwrap();
    assert(undo(returned).is_some());assert(eq(undo(returned).unwrap(),undo(state).unwrap()));
    assert(redo(undo(returned).unwrap()).is_some());
    assert(eq(redo(undo(returned).unwrap()).unwrap(),redo(undo(state).unwrap()).unwrap()));
    assert(eq(redo(undo(returned).unwrap()).unwrap(),state));
    assert(forward(redo(undo(returned).unwrap()).unwrap()).is_some());
}

/// In particular, foreign may be an old receipt's inverse. No inverse for
/// foreign, target enabledness, or desired whole-batch recovery is an input.
pub proof fn foreign_cross<S>(eq:spec_fn(S,S)->bool,redo:m::PartialMap<S>,
    undo:m::PartialMap<S>,foreign:m::PartialMap<S>,state:S)
    requires c::equivalence(eq),batch(eq,redo,undo,state),
        foreign(state).is_some(),p::respects(eq,foreign),
        p::commutes(eq,foreign,redo),p::commutes(eq,foreign,undo),
    ensures foreign(undo(state).unwrap()).is_some(),
        undo(foreign(state).unwrap()).is_some(),
        eq(undo(foreign(state).unwrap()).unwrap(),foreign(undo(state).unwrap()).unwrap()),
        batch(eq,redo,undo,foreign(state).unwrap()),
{
    let erased=undo(state).unwrap();let rebuilt=redo(erased).unwrap();
    assert(eq(rebuilt,state));assert(foreign(rebuilt).is_some());
    assert(p::optional_equal(eq,p::compose(foreign,redo)(erased),p::compose(redo,foreign)(erased)));
    assert(foreign(erased).is_some());assert(redo(foreign(erased).unwrap()).is_some());
    assert(eq(foreign(rebuilt).unwrap(),redo(foreign(erased).unwrap()).unwrap()));
    assert(eq(foreign(rebuilt).unwrap(),foreign(state).unwrap()));
    assert(p::optional_equal(eq,p::compose(foreign,undo)(state),p::compose(undo,foreign)(state)));
    assert(undo(foreign(state).unwrap()).is_some());
    assert(eq(undo(foreign(state).unwrap()).unwrap(),foreign(erased).unwrap()));
    assert(redo(undo(foreign(state).unwrap()).unwrap()).is_some());
    assert(eq(redo(undo(foreign(state).unwrap()).unwrap()).unwrap(),redo(foreign(erased).unwrap()).unwrap()));
}

/// The chronological actual own forward maps. strict_journal::journal keeps
/// exactly the same calls' inverses in the opposite execution order.
pub open spec fn forwards<S>(events:Seq<sj::Event<S>>)->Seq<m::PartialMap<S>>
    decreases events.len(),
{
    if events.len()==0 {Seq::empty()}
    else if events.last().own {forwards(events.drop_last()).push(events.last().forward)}
    else {forwards(events.drop_last())}
}
pub open spec fn redo<S>(events:Seq<sj::Event<S>>)->m::PartialMap<S> {
    |state:S|p::run(forwards(events),state)
}
pub open spec fn undo<S>(events:Seq<sj::Event<S>>)->m::PartialMap<S> {
    |state:S|p::run(sj::journal(events),state)
}

/// Only source calls are required to succeed. A foreign Event's inverse field
/// is ignored: the event can represent any respectful partial call, including
/// an inverse recovered from an older authentic receipt by a later bridge.
pub open spec fn admissible<S>(eq:spec_fn(S,S)->bool,events:Seq<sj::Event<S>>,initial:S)->bool
    decreases events.len(),
{
    events.len()==0 || {
        let prefix=events.drop_last();let e=events.last();let input=sj::trace(prefix,initial);
        &&& admissible(eq,prefix,initial)
        &&& input.is_some() && (e.forward)(input.unwrap()).is_some()
        &&& p::respects(eq,e.forward)
        &&& if e.own {
            &&& p::respects(eq,e.inverse)
            &&& (e.inverse)((e.forward)(input.unwrap()).unwrap()).is_some()
            &&& eq((e.inverse)((e.forward)(input.unwrap()).unwrap()).unwrap(),input.unwrap())
        } else {
            p::commutes(eq,e.forward,redo(prefix)) && p::commutes(eq,e.forward,undo(prefix))
        }
    }
}

/// Whole-batch reverse witnesses and strict erased replay are derived from
/// actual local own witnesses and the two explicit foreign crossing laws.
pub proof fn recovery<S>(eq:spec_fn(S,S)->bool,events:Seq<sj::Event<S>>,initial:S)
    requires c::equivalence(eq),admissible(eq,events,initial),
    ensures sj::recovered(eq,events,initial),
        batch(eq,redo(events),undo(events),sj::trace(events,initial).unwrap()),
    decreases events.len(),
{
    if events.len()==0 {
        empty_batch(eq,initial);
        assert(redo(events) =~= fu::identity());assert(undo(events) =~= fu::identity());
    } else {
        let prefix=events.drop_last();let e=events.last();recovery(eq,prefix,initial);
        let before=sj::trace(prefix,initial).unwrap();
        if e.own {
            own_push(eq,redo(prefix),undo(prefix),e.forward,e.inverse,before);
            assert(forwards(events).drop_last() =~= forwards(prefix));
            assert(forwards(events).last()==e.forward);
            assert(redo(events) =~= p::compose(e.forward,redo(prefix)));
            assert(undo(events) =~= p::compose(undo(prefix),e.inverse)) by {
                assert forall|state:S| #[trigger] undo(events)(state)==p::compose(undo(prefix),e.inverse)(state) by {
                    sj::run_prepend(e.inverse,sj::journal(prefix),state);
                }
            }
        } else {
            foreign_cross(eq,redo(prefix),undo(prefix),e.forward,before);
            let actual=undo(prefix)(before).unwrap();let target=sj::foreign(prefix,initial).unwrap();
            assert(eq(actual,target));assert((e.forward)(target).is_some());
            assert(eq((e.forward)(actual).unwrap(),(e.forward)(target).unwrap()));
        }
    }
}

pub proof fn every_prefix<S>(eq:spec_fn(S,S)->bool,events:Seq<sj::Event<S>>,initial:S)
    requires c::equivalence(eq),admissible(eq,events,initial),
    ensures forall|n:int| 0<=n<=events.len() ==> #[trigger] sj::recovered(eq,events.subrange(0,n),initial)
        && batch(eq,redo(events.subrange(0,n)),undo(events.subrange(0,n)),sj::trace(events.subrange(0,n),initial).unwrap()),
    decreases events.len(),
{
    recovery(eq,events,initial);
    if events.len()>0 {every_prefix(eq,events.drop_last(),initial);}
    assert forall|n:int| 0<=n<=events.len() implies #[trigger] sj::recovered(eq,events.subrange(0,n),initial)
        && batch(eq,redo(events.subrange(0,n)),undo(events.subrange(0,n)),sj::trace(events.subrange(0,n),initial).unwrap()) by {
        if n==events.len() {assert(events.subrange(0,n)==events);}
        else {assert(events.subrange(0,n)==events.drop_last().subrange(0,n));}
    }
}


pub open spec fn provision(key:int,value:int)->m::Node<int,int,()> {
    m::Node::Provision {key,value,next:None}
}
pub open spec fn operation(key:int,amount:int)->m::Node<int,int,()> {
    m::Node::Operation {key,operation:|v:int|Some(m::ValueYield {
        value:v+amount,undo:|w:int|Some(w-amount),outcome:()}),select:|_:()|None}
}
pub open spec fn values_equal()->spec_fn(int,int,int)->bool {|_key:int,a:int,b:int|a==b}
pub open spec fn tables_equal()->spec_fn(IMap<int,int>,IMap<int,int>)->bool {p::context_eq(values_equal())}
pub open spec fn captured(node:m::Node<int,int,()>,input:IMap<int,int>)->sj::Event<IMap<int,int>> {
    sj::Event {forward:p::forward(node),inverse:m::run(node,input).unwrap().undo,own:true}
}

pub proof fn example_theory(key:int,value:int,amount:int)
    ensures c::equivalence(tables_equal()),
        m::stage_respects(values_equal(),ISet::full(),provision(key,value)),m::stage_witness(provision(key,value)),
        m::stage_respects(values_equal(),ISet::full(),operation(key,amount)),m::stage_witness(operation(key,amount)),
{
    observation::context_equivalence(values_equal(),ISet::full());
    m::provision_admissible::<int,int,()>(values_equal(),ISet::full(),key,value,None);
    let op=|v:int|Some(m::ValueYield {value:v+amount,undo:|w:int|Some(w-amount),outcome:()});
    assert(m::operation_admissible(|a:int,b:int|a==b,op));
    m::operation_admissible_lift(values_equal(),ISet::full(),key,op,|_:()|None);
}
pub proof fn captured_contract(node:m::Node<int,int,()>,input:IMap<int,int>)
    requires c::equivalence(tables_equal()),m::run(node,input).is_some(),
        m::stage_respects(values_equal(),ISet::full(),node),m::stage_witness(node),
    ensures p::respects(tables_equal(),captured(node,input).forward),p::respects(tables_equal(),captured(node,input).inverse),
        (captured(node,input).forward)(input).is_some(),
        (captured(node,input).inverse)((captured(node,input).forward)(input).unwrap())==Some(input),
        p::generators(node).contains(captured(node,input).forward),p::generators(node).contains(captured(node,input).inverse),
{
    let e=captured(node,input);
    assert(p::generators(node).contains(e.inverse));
    p::generator_respects(values_equal(),node,e.forward);p::generator_respects(values_equal(),node,e.inverse);
}

pub open spec fn old_events()->Seq<sj::Event<IMap<int,int>>> {
    let first=captured(provision(0,9),IMap::empty());
    let second=captured(operation(0,1),(first.forward)(IMap::empty()).unwrap());
    seq![first,second]
}
pub open spec fn cut()->IMap<int,int> {IMap::empty().insert(0,10)}

/// These receipts come from actual successful Provision and Operation calls.
/// At value 10 the old Provision alone is not a reverse witness, although the
/// complete LIFO journal and chronological redo form a valid batch witness.
pub proof fn old_journal_is_not_individual_retractions()
    ensures admissible(tables_equal(),old_events(),IMap::empty()),
        sj::trace(old_events(),IMap::empty())==Some(cut()),
        batch(tables_equal(),redo(old_events()),undo(old_events()),cut()),
        undo(old_events())(cut())==Some(IMap::empty()),
        redo(old_events())(IMap::empty())==Some(cut()),
        !fu::retracts(tables_equal(),fu::Pair {forward:old_events()[0].forward,inverse:old_events()[0].inverse,own:false},cut()),
        m::run(provision(0,9),IMap::empty()).is_some(),
        m::run(operation(0,1),IMap::empty().insert(0,9)).is_some(),
{
    example_theory(0,9,1);
    captured_contract(provision(0,9),IMap::empty());
    captured_contract(operation(0,1),IMap::empty().insert(0,9));
    let events=old_events();
    assert(IMap::<int,int>::empty().insert(0,9).insert(0,10) =~= cut());
    reveal_with_fuel(admissible,3);reveal_with_fuel(sj::trace,3);
    assert(admissible(tables_equal(),events,IMap::empty()));recovery(tables_equal(),events,IMap::empty());
    assert(cut().insert(0,9).remove(0) =~= IMap::empty());
    reveal_with_fuel(forwards,3);reveal_with_fuel(sj::journal,3);reveal_with_fuel(p::run,3);
    assert(cut().remove(0) =~= IMap::empty());
    assert(!tables_equal()(IMap::empty().insert(0,9),cut())) by {
        let low=IMap::<int,int>::empty().insert(0,9);
        assert(low.dom().contains(0));assert(cut().dom().contains(0));
        assert(!values_equal()(0,low[0],cut()[0]));
        if observation::context_equal(values_equal(),ISet::full(),low,cut()) {
            assert(ISet::<int>::full().contains(0));
            assert(values_equal()(0,low[0],cut()[0]));
        }
        assert(!observation::context_equal(values_equal(),ISet::full(),low,cut()));
    }
}

pub open spec fn interleaving()->Seq<sj::Event<IMap<int,int>>> {
    let a=captured(provision(1,23),cut());
    let b=captured(operation(1,4),(a.forward)(cut()).unwrap());
    // Only the actual old inverse is executed: no synthetic reverse witness
    // is read from these foreign events' deliberately unused inverse field.
    seq![a,b,
        sj::Event {forward:old_events()[1].inverse,inverse:|_:IMap<int,int>|None,own:false},
        sj::Event {forward:old_events()[0].inverse,inverse:|_:IMap<int,int>|None,own:false}]
}

pub proof fn disjoint_captured(left:m::Node<int,int,()>,right:m::Node<int,int,()>,a:IMap<int,int>,b:IMap<int,int>)
    requires c::equivalence(tables_equal()),m::run(left,a).is_some(),m::run(right,b).is_some(),
        m::stage_respects(values_equal(),ISet::full(),left),m::stage_respects(values_equal(),ISet::full(),right),
        p::key(left).is_some(),p::key(right).is_some(),p::key(left)!=p::key(right),
    ensures p::commutes(tables_equal(),captured(left,a).forward,captured(right,b).inverse),
        p::commutes(tables_equal(),captured(left,a).inverse,captured(right,b).inverse),
{
    let x=captured(left,a);let y=captured(right,b);
    assert(p::generators(left).contains(x.forward));assert(p::generators(left).contains(x.inverse));
    assert(p::generators(right).contains(y.inverse));
    p::distinct_nodes(values_equal(),left,right);
}

/// A fresh own Provision/Operation batch surrounds a complete old foreign
/// journal's LIFO cleanup. The old journal starts before this segment: its
/// actual receipts, rather than a new forward call, supply both foreign maps.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn old_inverse_interleaving()
    ensures admissible(tables_equal(),interleaving(),cut()),
        !sj::admissible(tables_equal(),interleaving(),cut()),
        sj::trace(interleaving(),cut())==Some(IMap::empty().insert(1,27)),
        sj::foreign(interleaving(),cut())==Some(IMap::empty()),
        undo(interleaving())(IMap::empty().insert(1,27))==Some(IMap::empty()),
        batch(tables_equal(),redo(interleaving()),undo(interleaving()),IMap::empty().insert(1,27)),
        !fu::retracts(tables_equal(),fu::Pair {forward:old_events()[0].forward,inverse:old_events()[0].inverse,own:false},cut()),
{
    old_journal_is_not_individual_retractions();example_theory(1,23,4);
    let a=provision(1,23);let b=operation(1,4);let ai=cut();let bi=cut().insert(1,23);
    let olda=provision(0,9);let oldb=operation(0,1);let oldai=IMap::<int,int>::empty();let oldbi=oldai.insert(0,9);
    captured_contract(a,ai);captured_contract(b,bi);
    disjoint_captured(a,olda,ai,oldai);disjoint_captured(b,olda,bi,oldai);
    disjoint_captured(a,oldb,ai,oldbi);disjoint_captured(b,oldb,bi,oldbi);
    let events=interleaving();let prefix=events.subrange(0,2);
    reveal_with_fuel(forwards,5);reveal_with_fuel(sj::journal,5);reveal_with_fuel(sj::trace,5);reveal_with_fuel(sj::foreign,5);
    assert(forwards(prefix)==seq![captured(a,ai).forward,captured(b,bi).forward]);
    assert(sj::journal(prefix)==seq![captured(b,bi).inverse,captured(a,ai).inverse]);
    assert(sj::respects(tables_equal(),forwards(prefix)));assert(sj::respects(tables_equal(),sj::journal(prefix)));
    assert(sj::crosses(tables_equal(),forwards(prefix),old_events()[1].inverse));
    assert(sj::crosses(tables_equal(),sj::journal(prefix),old_events()[1].inverse));
    assert(sj::crosses(tables_equal(),forwards(prefix),old_events()[0].inverse));
    assert(sj::crosses(tables_equal(),sj::journal(prefix),old_events()[0].inverse));
    sj::word_commutes(tables_equal(),forwards(prefix),old_events()[1].inverse);
    sj::word_commutes(tables_equal(),sj::journal(prefix),old_events()[1].inverse);
    sj::word_commutes(tables_equal(),forwards(prefix),old_events()[0].inverse);
    sj::word_commutes(tables_equal(),sj::journal(prefix),old_events()[0].inverse);
    assert(forwards(events.subrange(0,3))==forwards(prefix));assert(sj::journal(events.subrange(0,3))==sj::journal(prefix));
    assert(cut().insert(1,23).insert(1,27).insert(0,9).remove(0) =~= IMap::empty().insert(1,27));
    assert(cut().insert(0,9).remove(0) =~= IMap::empty());
    reveal_with_fuel(admissible,5);assert(admissible(tables_equal(),events,cut()));
    recovery(tables_equal(),events,cut());
    reveal_with_fuel(sj::admissible,5);
    assert(IMap::<int,int>::empty().insert(1,27).insert(1,23).remove(1) =~= IMap::empty());
    reveal_with_fuel(p::run,3);
}


/// The redo crossing law cannot be replaced by undo commutation alone.
/// Both undo/foreign composites fail, yet the source foreign call succeeds.
pub proof fn undo_commutation_alone_is_insufficient()
    ensures {
        let eq=|a:int,b:int|a==b;
        let redo=|s:int|if s==0 {Some(1int)} else {None};
        let undo=|s:int|if s==1 {Some(0int)} else {None};
        let foreign=|s:int|if s==1 {Some(2int)} else {None};
        &&& batch(eq,redo,undo,1) && p::respects(eq,foreign)
        &&& foreign(1)==Some(2int) && foreign(undo(1).unwrap()).is_none()
        &&& p::commutes(eq,foreign,undo) && !p::commutes(eq,foreign,redo)
    },
{
    let eq=|a:int,b:int|a==b;
    let redo=|s:int|if s==0 {Some(1int)} else {None};
    let undo=|s:int|if s==1 {Some(0int)} else {None};
    let foreign=|s:int|if s==1 {Some(2int)} else {None};
    assert forall|s:int| #[trigger] p::optional_equal(eq,p::compose(foreign,undo)(s),p::compose(undo,foreign)(s)) by {}
    assert(!p::optional_equal(eq,p::compose(foreign,redo)(0),p::compose(redo,foreign)(0)));
}

} // verus!
