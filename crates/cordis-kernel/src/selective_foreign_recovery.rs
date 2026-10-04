//! Strict recovery with foreign historical retractions only.
//!
//! Own calls require their ordinary local inverse witness and LIFO recovery.
//! They need not commute with themselves or other own calls. Only foreign
//! records retain reverse witnesses through subsequent calls, which admits
//! strict Provision/revoke pairs without inventing self-commutation.
#[cfg(verus_keep_ghost)]
use crate::{
    calculus as c,
    foreign_unload::{self as fu, Action, Pair},
    partial_independence as p, strict_journal as sj,
};
use vstd::prelude::*;

verus! {
pub open spec fn theory<S>(eq:spec_fn(S,S)->bool,records:Seq<Pair<S>>)->bool {
    &&& forall|i:int| 0<=i<records.len() ==> fu::respectful(eq,#[trigger] records[i])
    &&& forall|i:int,j:int| 0<=i<records.len() && 0<=j<records.len() ==> (!records[i].own || !records[j].own) ==> fu::compatible(eq,#[trigger] records[i],#[trigger] records[j])
}
pub open spec fn catalog_retracts<S>(eq:spec_fn(S,S)->bool,records:Seq<Pair<S>>,state:S)->bool {
    forall|i:int| 0<=i<records.len() ==> !records[i].own ==> fu::retracts(eq,#[trigger] records[i],state)
}

/// Only new actual forward calls supply their ordinary local inverse witness.
/// Authentic inverse calls select a prior record; their enabledness and reverse
/// witness are conclusions. No whole restore or surviving trace is a premise.
pub open spec fn local_source<S>(eq:spec_fn(S,S)->bool,actions:Seq<Action<S>>,initial:S)->bool
    decreases actions.len(),
{
    actions.len()==0 || {
        let prefix=actions.drop_last();let records=fu::catalog(prefix);let input=sj::trace(fu::events(prefix),initial);
        &&& local_source(eq,prefix,initial)
        &&& match actions.last() {
            Action::Forward {call}=>{
                &&& input.is_some() && (call.forward)(input.unwrap()).is_some()
                &&& (call.inverse)((call.forward)(input.unwrap()).unwrap()).is_some()
                &&& eq((call.inverse)((call.forward)(input.unwrap()).unwrap()).unwrap(),input.unwrap())
                &&& fu::respectful(eq,call) && (!call.own ==> fu::compatible(eq,call,call))
                &&& forall|i:int| 0<=i<records.len() ==> (!records[i].own || !call.own) ==> fu::compatible(eq,#[trigger] records[i],call) && fu::compatible(eq,call,#[trigger] records[i])
            },
            Action::Inverse {token}=>token<records.len() && !records[token as int].own,
            Action::Identity=>true,
        }
    }
}

pub proof fn catalog_theory<S>(eq:spec_fn(S,S)->bool,actions:Seq<Action<S>>,initial:S)
    requires local_source(eq,actions,initial),
    ensures theory(eq,fu::catalog(actions)),
    decreases actions.len(),
{
    if actions.len()>0 {
        let prefix=actions.drop_last();catalog_theory(eq,prefix,initial);
        let before=fu::catalog(prefix);let records=fu::catalog(actions);
        if let Action::Forward {call}=actions.last() {
            assert forall|i:int| 0<=i<records.len() implies fu::respectful(eq,#[trigger] records[i]) by {
                if i<before.len() {assert(records[i]==before[i]);} else {assert(i==before.len());}
            }
            assert forall|i:int,j:int| 0<=i<records.len() && 0<=j<records.len() && (!records[i].own || !records[j].own) implies fu::compatible(eq,#[trigger] records[i],#[trigger] records[j]) by {
                if i<before.len() {assert(records[i]==before[i]);}
                if j<before.len() {assert(records[j]==before[j]);}
            }
        }
    }
}
pub proof fn source_invariant<S>(eq:spec_fn(S,S)->bool,actions:Seq<Action<S>>,initial:S)
    requires c::equivalence(eq),local_source(eq,actions,initial),
    ensures sj::trace(fu::events(actions),initial).is_some(),catalog_retracts(eq,fu::catalog(actions),sj::trace(fu::events(actions),initial).unwrap()),
        sj::admissible(eq,fu::events(actions),initial),
    decreases actions.len(),
{
    catalog_theory(eq,actions,initial);fu::journal_origins(actions);
    if actions.len()>0 {
        let prefix=actions.drop_last();source_invariant(eq,prefix,initial);catalog_theory(eq,prefix,initial);fu::journal_origins(prefix);
        let records=fu::catalog(prefix);let all=fu::catalog(actions);let es=fu::events(prefix);let e=fu::event(records,actions.last());let before=sj::trace(es,initial).unwrap();
        assert(fu::events(actions).drop_last() =~= es);
        match actions.last() {
            Action::Forward {call}=>{fu::local_forward_retracts(eq,call,before);},
            Action::Inverse {token}=>{assert(fu::retracts(eq,records[token as int],before));},
            Action::Identity=>{fu::identity_contract(eq,fu::identity::<S>());assert(eq(before,before));},
        }
        assert((e.forward)(before).is_some());let after=(e.forward)(before).unwrap();
        assert((e.inverse)(after).is_some());assert(eq((e.inverse)(after).unwrap(),before));
        assert(p::respects(eq,e.forward));
        assert forall|i:int| 0<=i<all.len() && !all[i].own implies fu::retracts(eq,#[trigger] all[i],after) by {
            if i<records.len() {
                assert(all[i]==records[i]);assert(fu::retracts(eq,records[i],before));
                match actions.last() {
                    Action::Forward {call}=>{assert(fu::compatible(eq,call,records[i]));assert(fu::compatible(eq,records[i],call));},
                    Action::Inverse {token}=>{assert(fu::compatible(eq,records[token as int],records[i]));assert(fu::compatible(eq,records[i],records[token as int]));},
                    Action::Identity=>{fu::identity_contract(eq,records[i].forward);fu::identity_contract(eq,records[i].inverse);p::commute_symmetric(eq,records[i].inverse,fu::identity());},
                }
                fu::transport_retraction(eq,records[i],e.forward,e.inverse,before);
            } else {assert(i==records.len());}
        }
        if !e.own {
            assert forall|i:int| 0<=i<sj::journal(es).len() implies p::commutes(eq,#[trigger] sj::journal(es)[i],e.forward)
                && p::commutes(eq,sj::journal(es)[i],e.inverse) by {
                let j=choose|j:int| 0<=j<records.len() && records[j].own && records[j].inverse==sj::journal(es)[i];
                match actions.last() {
                    Action::Forward {call}=>{assert(fu::compatible(eq,records[j],call));},
                    Action::Inverse {token}=>{assert(fu::compatible(eq,records[j],records[token as int]));},
                    Action::Identity=>{fu::identity_contract(eq,records[j].inverse);},
                }
            }
        }
    }
}

pub proof fn recovery_with_foreign_inverses<S>(eq:spec_fn(S,S)->bool,actions:Seq<Action<S>>,initial:S)
    requires c::equivalence(eq),local_source(eq,actions,initial),
    ensures sj::recovered(eq,fu::events(actions),initial),
{
    source_invariant(eq,actions,initial);sj::recovery(eq,fu::events(actions),initial);
}


/// The previous all-record contract is a special case; no existing theorem
/// needs to weaken its semantics to use this catalogue.
pub proof fn previous_contract<S>(eq:spec_fn(S,S)->bool,actions:Seq<Action<S>>,initial:S)
    requires fu::local_source(eq,actions,initial),
    ensures local_source(eq,actions,initial),
    decreases actions.len(),
{
    if actions.len()>0 {previous_contract(eq,actions.drop_last(),initial);}
}

pub open spec fn provision()->Pair<(Option<int>,int)> {
    Pair {forward:|s:(Option<int>,int)|if s.0.is_none() {Some((Some(9int),s.1))} else {None},
        inverse:|s:(Option<int>,int)|if s.0.is_some() {Some((None,s.1))} else {None},own:true}
}
pub open spec fn shift(amount:int,own:bool)->Pair<(Option<int>,int)> {
    Pair {forward:|s:(Option<int>,int)|Some((s.0,s.1+amount)),inverse:|s:(Option<int>,int)|Some((s.0,s.1-amount)),own}
}
pub proof fn provision_shift_commutes(amount:int,own:bool)
    ensures fu::respectful(|a:(Option<int>,int),b:(Option<int>,int)|a==b,provision()),
        fu::compatible(|a:(Option<int>,int),b:(Option<int>,int)|a==b,provision(),shift(amount,own)),
        fu::compatible(|a:(Option<int>,int),b:(Option<int>,int)|a==b,shift(amount,own),provision()),
{
    let eq=|a:(Option<int>,int),b:(Option<int>,int)|a==b;let a=provision();let b=shift(amount,own);
    assert forall|s:(Option<int>,int)| #[trigger] p::optional_equal(eq,p::compose(a.forward,b.forward)(s),p::compose(b.forward,a.forward)(s)) by {}
    assert forall|s:(Option<int>,int)| #[trigger] p::optional_equal(eq,p::compose(a.forward,b.inverse)(s),p::compose(b.inverse,a.forward)(s)) by {}
    assert forall|s:(Option<int>,int)| #[trigger] p::optional_equal(eq,p::compose(a.inverse,b.forward)(s),p::compose(b.forward,a.inverse)(s)) by {}
    assert forall|s:(Option<int>,int)| #[trigger] p::optional_equal(eq,p::compose(a.inverse,b.inverse)(s),p::compose(b.inverse,a.inverse)(s)) by {}
    p::commute_symmetric(eq,a.forward,b.forward);p::commute_symmetric(eq,a.forward,b.inverse);p::commute_symmetric(eq,a.inverse,b.forward);p::commute_symmetric(eq,a.inverse,b.inverse);
}
pub proof fn shifts_commute(left:int,right:int,a:bool,b:bool)
    ensures fu::respectful(|a:(Option<int>,int),b:(Option<int>,int)|a==b,shift(left,a)),
        fu::compatible(|a:(Option<int>,int),b:(Option<int>,int)|a==b,shift(left,a),shift(right,b)),
{
    let eq=|a:(Option<int>,int),b:(Option<int>,int)|a==b;let x=shift(left,a);let y=shift(right,b);
    assert forall|s:(Option<int>,int)| #[trigger] p::optional_equal(eq,p::compose(x.forward,y.forward)(s),p::compose(y.forward,x.forward)(s)) by {}
    assert forall|s:(Option<int>,int)| #[trigger] p::optional_equal(eq,p::compose(x.forward,y.inverse)(s),p::compose(y.inverse,x.forward)(s)) by {}
    assert forall|s:(Option<int>,int)| #[trigger] p::optional_equal(eq,p::compose(x.inverse,y.forward)(s),p::compose(y.forward,x.inverse)(s)) by {}
    assert forall|s:(Option<int>,int)| #[trigger] p::optional_equal(eq,p::compose(x.inverse,y.inverse)(s),p::compose(y.inverse,x.inverse)(s)) by {}
}
/// Provision is admitted with its genuinely strict create/revoke domains.
/// Shared value shifts and an authentic foreign inverse interleave with it.
pub proof fn provision_with_foreign_inverse()
    ensures {
        let eq=|a:(Option<int>,int),b:(Option<int>,int)|a==b;let initial=(None,0int);
        let actions=seq![Action::Forward {call:provision()},Action::Forward {call:shift(5,true)},Action::Forward {call:shift(7,false)},Action::Inverse {token:2nat}];
        &&& local_source(eq,actions,initial) && !fu::local_source(eq,actions,initial)
        &&& sj::trace(fu::events(actions),initial)==Some((Some(9int),5int))
        &&& sj::foreign(fu::events(actions),initial)==Some(initial)
        &&& p::run(sj::journal(fu::events(actions)),(Some(9int),5int))==Some(initial)
        &&& !fu::compatible(eq,provision(),provision())
    },
{
    let eq=|a:(Option<int>,int),b:(Option<int>,int)|a==b;let initial=(None,0int);let a=provision();
    let actions=seq![Action::Forward {call:a},Action::Forward {call:shift(5,true)},Action::Forward {call:shift(7,false)},Action::Inverse {token:2nat}];
    provision_shift_commutes(5,true);provision_shift_commutes(7,false);shifts_commute(5,7,true,false);shifts_commute(7,5,false,true);shifts_commute(7,7,false,false);
    assert(!p::optional_equal(eq,p::compose(a.forward,a.inverse)(initial),p::compose(a.inverse,a.forward)(initial)));
    assert(!p::commutes(eq,a.forward,a.inverse));assert(!fu::compatible(eq,a,a));
    reveal_with_fuel(local_source,5);reveal_with_fuel(fu::local_source,5);reveal_with_fuel(fu::events,5);reveal_with_fuel(fu::catalog,5);reveal_with_fuel(sj::trace,5);
    assert(local_source(eq,actions,initial));recovery_with_foreign_inverses(eq,actions,initial);reveal_with_fuel(sj::foreign,5);
}

} // verus!
