//! Recovery with strict partial domains and actual local inverse witnesses.
//!
//! Foreign events carry the inverse returned by that actual forward call.
//! Pairwise commutation with pending own inverses derives restoration and
//! foreign replay definedness; neither whole-trace property is a premise.
//! This algebra does not by itself cover an arbitrary foreign Unload, whose
//! current inverse call need not carry an inverse witness of its own.
use crate::mediated as m;
#[cfg(verus_keep_ghost)]
use crate::{calculus as c, partial_domains as domains, partial_independence as p};
use vstd::prelude::*;

verus! {

#[verifier::reject_recursive_types(S)]
pub struct Event<S> {
    pub forward:m::PartialMap<S>,
    pub inverse:m::PartialMap<S>,
    pub own:bool,
}

pub open spec fn trace<S>(events:Seq<Event<S>>,initial:S)->Option<S>
    decreases events.len(),
{
    if events.len()==0 {Some(initial)}
    else {match trace(events.drop_last(),initial) {Some(before)=>(events.last().forward)(before),None=>None}}
}

/// Inverses in actual execution order: the newest own inverse runs first.
pub open spec fn journal<S>(events:Seq<Event<S>>)->Seq<m::PartialMap<S>>
    decreases events.len(),
{
    if events.len()==0 {Seq::empty()}
    else if events.last().own {seq![events.last().inverse]+journal(events.drop_last())}
    else {journal(events.drop_last())}
}

pub open spec fn foreign<S>(events:Seq<Event<S>>,initial:S)->Option<S>
    decreases events.len(),
{
    if events.len()==0 {Some(initial)}
    else if events.last().own {foreign(events.drop_last(),initial)}
    else {match foreign(events.drop_last(),initial) {Some(before)=>(events.last().forward)(before),None=>None}}
}

pub open spec fn respects<S>(eq:spec_fn(S,S)->bool,word:Seq<m::PartialMap<S>>)->bool {
    forall|i:int| 0<=i<word.len() ==> p::respects(eq,#[trigger] word[i])
}
pub open spec fn crosses<S>(eq:spec_fn(S,S)->bool,word:Seq<m::PartialMap<S>>,f:m::PartialMap<S>)->bool {
    forall|i:int| 0<=i<word.len() ==> p::commutes(eq,#[trigger] word[i],f)
}

/// Conditions mention only the source prefix, its real returned journal and
/// the new event's actual input. No recovery, erased replay or enabled inverse
/// at a later input is assumed.
pub open spec fn admissible<S>(eq:spec_fn(S,S)->bool,events:Seq<Event<S>>,initial:S)->bool
    decreases events.len(),
{
    events.len()==0 || {
        let prefix=events.drop_last();let e=events.last();let before=trace(prefix,initial);
        &&& admissible(eq,prefix,initial)
        &&& before.is_some() && (e.forward)(before.unwrap()).is_some()
        &&& (e.inverse)((e.forward)(before.unwrap()).unwrap()).is_some()
        &&& eq((e.inverse)((e.forward)(before.unwrap()).unwrap()).unwrap(),before.unwrap())
        &&& p::respects(eq,e.forward)
        &&& if e.own {p::respects(eq,e.inverse)} else {
            crosses(eq,journal(prefix),e.forward) && crosses(eq,journal(prefix),e.inverse)
        }
    }
}

pub proof fn run_prepend<S>(first:m::PartialMap<S>,rest:Seq<m::PartialMap<S>>,input:S)
    ensures p::run(seq![first]+rest,input)==match first(input) {Some(s)=>p::run(rest,s),None=>None},
    decreases rest.len(),
{
    if rest.len()==0 {assert(seq![first]+rest==seq![first]);reveal_with_fuel(p::run,2);}
    else {
        let whole=seq![first]+rest;
        assert(whole.drop_last() =~= seq![first]+rest.drop_last());assert(whole.last()==rest.last());
        run_prepend(first,rest.drop_last(),input);
    }
}

pub proof fn journal_respects<S>(eq:spec_fn(S,S)->bool,events:Seq<Event<S>>,initial:S)
    requires admissible(eq,events,initial),
    ensures respects(eq,journal(events)),
    decreases events.len(),
{
    if events.len()>0 {
        let prefix=events.drop_last();journal_respects(eq,prefix,initial);
        if events.last().own {
            assert forall|i:int| 0<=i<journal(events).len() implies p::respects(eq,#[trigger] journal(events)[i]) by {
                if i==0 {assert(journal(events)[i]==events.last().inverse);}
                else {assert(journal(events)[i]==journal(prefix)[i-1]);}
            }
        }
    }
}

pub proof fn word_commutes<S>(eq:spec_fn(S,S)->bool,word:Seq<m::PartialMap<S>>,f:m::PartialMap<S>)
    requires c::equivalence(eq),respects(eq,word),crosses(eq,word,f),
    ensures p::commutes(eq,|s:S|p::run(word,s),f),p::commutes(eq,f,|s:S|p::run(word,s)),
{
    assert forall|i:int| 0<=i<word.len() implies p::commutes(eq,f,#[trigger] word[i]) && p::respects(eq,word[i]) by {
        p::commute_symmetric(eq,word[i],f);
    }
    p::commute_word(eq,f,word);p::commute_symmetric(eq,f,|s:S|p::run(word,s));
}

/// All pending own inverses can actually execute. Erasing own events also
/// yields a defined strict partial replay, observationally equal to recovery.
pub proof fn recovery<S>(eq:spec_fn(S,S)->bool,events:Seq<Event<S>>,initial:S)
    requires c::equivalence(eq),admissible(eq,events,initial),
    ensures trace(events,initial).is_some(),foreign(events,initial).is_some(),
        p::run(journal(events),trace(events,initial).unwrap()).is_some(),
        eq(p::run(journal(events),trace(events,initial).unwrap()).unwrap(),foreign(events,initial).unwrap()),
    decreases events.len(),
{
    journal_respects(eq,events,initial);
    if events.len()>0 {
        let prefix=events.drop_last();let e=events.last();recovery(eq,prefix,initial);
        let before=trace(prefix,initial).unwrap();let after=(e.forward)(before).unwrap();
        let word=journal(prefix);let restore=|s:S|p::run(word,s);
        journal_respects(eq,prefix,initial);p::run_respects(eq,word);
        if e.own {
            let recovered=(e.inverse)(after).unwrap();
            assert(eq(recovered,before));
            assert(restore(recovered).is_some());assert(eq(restore(recovered).unwrap(),restore(before).unwrap()));
            run_prepend(e.inverse,word,after);
        } else {
            word_commutes(eq,word,e.forward);word_commutes(eq,word,e.inverse);
            domains::enabled_diamond(eq,e.forward,restore,e.inverse,before);
            let recovered=restore(before).unwrap();let replay=foreign(prefix,initial).unwrap();
            assert(eq(recovered,replay));assert((e.forward)(replay).is_some());
            assert(eq((e.forward)(recovered).unwrap(),(e.forward)(replay).unwrap()));
            assert(eq(restore(after).unwrap(),(e.forward)(recovered).unwrap()));
        }
    }
}

pub open spec fn recovered<S>(eq:spec_fn(S,S)->bool,events:Seq<Event<S>>,initial:S)->bool {
    &&& trace(events,initial).is_some() && foreign(events,initial).is_some()
    &&& p::run(journal(events),trace(events,initial).unwrap()).is_some()
    &&& eq(p::run(journal(events),trace(events,initial).unwrap()).unwrap(),foreign(events,initial).unwrap())
}

pub proof fn every_prefix<S>(eq:spec_fn(S,S)->bool,events:Seq<Event<S>>,initial:S)
    requires c::equivalence(eq),admissible(eq,events,initial),
    ensures forall|n:int| 0<=n<=events.len() ==> #[trigger] recovered(eq,events.subrange(0,n),initial),
    decreases events.len(),
{
    recovery(eq,events,initial);
    if events.len()>0 {every_prefix(eq,events.drop_last(),initial);}
    assert forall|n:int| 0<=n<=events.len() implies #[trigger] recovered(eq,events.subrange(0,n),initial) by {
        if n==events.len() {assert(events.subrange(0,n)==events);}
        else {assert(events.subrange(0,n)==events.drop_last().subrange(0,n));}
    }
}

pub open spec fn shift(amount:int)->m::PartialMap<(bool,int)> {
    |s:(bool,int)|if s.0 {Some((true,s.1+amount))} else {None}
}
pub proof fn shift_commutes(left:int,right:int)
    ensures p::commutes(|a:(bool,int),b:(bool,int)|a==b,shift(left),shift(right)),
{
    let eq=|a:(bool,int),b:(bool,int)|a==b;
    assert forall|s:(bool,int)| #[trigger] p::optional_equal(eq,p::compose(shift(left),shift(right))(s),p::compose(shift(right),shift(left))(s)) by { }
}

/// A strict, partially defined same-key example with two own inverses around
/// a foreign event. Failed inputs remain failed; recovery is genuinely defined.
pub proof fn strict_interleaving()
    ensures {
        let events=seq![Event {forward:shift(5),inverse:shift(-5),own:true},
            Event {forward:shift(3),inverse:shift(-3),own:false},
            Event {forward:shift(2),inverse:shift(-2),own:true}];
        &&& admissible(|a:(bool,int),b:(bool,int)|a==b,events,(true,0int))
        &&& trace(events,(true,0int))==Some((true,10int))
        &&& p::run(journal(events),(true,10int))==Some((true,3int))
        &&& foreign(events,(true,0int))==Some((true,3int))
        &&& trace(events,(false,0int)).is_none()
    },
{
    let eq=|a:(bool,int),b:(bool,int)|a==b;
    let events=seq![Event {forward:shift(5),inverse:shift(-5),own:true},
        Event {forward:shift(3),inverse:shift(-3),own:false},
        Event {forward:shift(2),inverse:shift(-2),own:true}];
    shift_commutes(-5,3);shift_commutes(-5,-3);
    reveal_with_fuel(trace,4);reveal_with_fuel(journal,4);reveal_with_fuel(foreign,4);reveal_with_fuel(admissible,4);
    assert(admissible(eq,events,(true,0int)));recovery(eq,events,(true,0int));
}

/// Commutation with the foreign forward alone cannot keep a pending inverse
/// enabled. Its actual returned witness is a necessary part of the interface.
pub proof fn forward_commutation_does_not_preserve_domain()
    ensures {
        let own=Event {forward:|s:int|if s==0 {Some(1int)} else {None},inverse:|s:int|if s==1 {Some(0int)} else {None},own:true};
        let other=Event {forward:|s:int|if s==1 {Some(2int)} else {None},inverse:|s:int|if s==2 {Some(1int)} else {None},own:false};
        let events=seq![own,other];let eq=|a:int,b:int|a==b;
        &&& trace(events,0)==Some(2int)
        &&& (other.inverse)((other.forward)(1).unwrap())==Some(1int)
        &&& p::commutes(eq,own.inverse,other.forward)
        &&& !p::commutes(eq,own.inverse,other.inverse)
        &&& p::run(journal(events),2).is_none() && foreign(events,0).is_none()
        &&& !admissible(eq,events,0)
    },
{
    let own=Event {forward:|s:int|if s==0 {Some(1int)} else {None},inverse:|s:int|if s==1 {Some(0int)} else {None},own:true};
    let other=Event {forward:|s:int|if s==1 {Some(2int)} else {None},inverse:|s:int|if s==2 {Some(1int)} else {None},own:false};
    let eq=|a:int,b:int|a==b;
    assert forall|s:int| #[trigger] p::optional_equal(eq,p::compose(own.inverse,other.forward)(s),p::compose(other.forward,own.inverse)(s)) by { }
    assert(!p::optional_equal(eq,p::compose(own.inverse,other.inverse)(2),p::compose(other.inverse,own.inverse)(2)));
    reveal_with_fuel(trace,3);reveal_with_fuel(journal,3);reveal_with_fuel(foreign,3);reveal_with_fuel(admissible,3);
    let events=seq![own,other];
    assert(trace(events,0)==Some(2int));
    assert(p::commutes(eq,own.inverse,other.forward));
    assert(!p::commutes(eq,own.inverse,other.inverse));
    assert(journal(events)==seq![own.inverse]);reveal_with_fuel(p::run,2);
    assert(p::run(journal(events),2).is_none());assert(foreign(events,0).is_none());
    assert(!crosses(eq,journal(seq![own]),other.inverse)) by {assert(journal(seq![own])[0]==own.inverse);}
    assert(!admissible(eq,events,0));
}

} // verus!
