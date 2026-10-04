//! Dynamic child provenance connected to actual lifecycle accumulators.
//!
//! External insertion retains its general parent option. Only children born by
//! a lifecycle primitive receive a `Birth`; an explicit additional root-only
//! orchestration profile yields the parent clause used by paper Lemma 77.
//! Recovery premises describe the actual primitive inverse at every LIFO
//! position. They do not assert a restored state or a retirement invariant.
#[cfg(verus_keep_ghost)]
use crate::{global, preservation as p, refinement as c, semantics as s, Phase};
use vstd::prelude::*;

verus! {

pub struct Birth {
    pub parent: usize,
    pub episode: nat,
    pub landed_at: nat,
    pub inverse: nat,
}

pub struct History {
    pub time: nat,
    pub episode: spec_fn(usize) -> nat,
    pub births: IMap<usize, Birth>,
}

pub open spec fn initial() -> History {
    History { time: 0, episode: |_:usize| 0, births: IMap::empty() }
}

/// The classification denotes the meaning of an actual inverse identity.
/// A child inverse must name the child returned by its own creation primitive.
pub open spec fn forward<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,a:s::State<V>,n:usize) -> bool {
    let y = (model.iterate)(n,a.iterators[n].unwrap(),a);
    match kind(y.inverse) {
        None => p::table_map(a,y.state,n),
        Some(child) => p::child_map(a,y.state,n,child),
    }
}

pub open spec fn inverse<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,a:s::State<V>,n:usize,token:nat) -> bool {
    match kind(token) {
        None => p::table_map(a,(model.undo)(token,a),n),
        Some(child) => s::child_retire(a,(model.undo)(token,a),child),
    }
}

/// Strict Definition 52 inverses need the child to remain registered. This
/// recursive local contract deliberately exposes that domain obligation.
pub open spec fn recovery<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,tokens:Seq<nat>,a:s::State<V>,n:usize) -> bool
    decreases tokens.len(),
{
    tokens.len() == 0 || (inverse(model,kind,a,n,tokens.last())
        && recovery(model,kind,tokens.drop_last(),(model.undo)(tokens.last(),a),n))
}

pub open spec fn landing<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,n:usize,rule:c::Rule) -> bool {
    rule == c::Rule::Iter || rule == c::Rule::Finish || (rule == c::Rule::Divert
        && z != s::edit(a,n,Phase::Unloading,a.control.fibers[n].committed,None,a.accumulators[n]))
}

pub open spec fn admissible<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,a:s::State<V>,z:s::State<V>,n:usize,rule:c::Rule) -> bool {
    &&& p::admissible_step(model,a,z,n,rule)
    &&& (landing(model,a,z,n,rule) ==> forward(model,kind,a,n))
    &&& (rule == c::Rule::Unload ==> recovery(model,kind,a.accumulators[n],a,n))
}

/// Ghost update calculated from the real yielded inverse, never supplied as a
/// successor invariant. A new Begin receives a distinct trace-position ID.
pub open spec fn advance<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,h:History,a:s::State<V>,z:s::State<V>,n:usize,rule:c::Rule) -> History {
    let births = if rule == c::Rule::Remove || rule == c::Rule::Insert {
        h.births.remove(n)
    } else if landing(model,a,z,n,rule) {
        let y = (model.iterate)(n,a.iterators[n].unwrap(),a);
        match kind(y.inverse) {
            None => h.births,
            Some(child) => h.births.insert(child,Birth {parent:n,episode:(h.episode)(n),landed_at:h.time+1,inverse:y.inverse}),
        }
    } else { h.births };
    History { time:h.time+1,
        episode:|m:usize| if m == n && rule == c::Rule::Begin { h.time+1 }
            else if (m == n && rule == c::Rule::Insert)
                || (landing(model,a,z,n,rule) && kind((model.iterate)(n,a.iterators[n].unwrap(),a).inverse) == Some(m))
                { 0 } else { (h.episode)(m) },
        births }
}

pub open spec fn valid<V>(kind:spec_fn(nat)->Option<usize>,h:History,a:s::State<V>) -> bool {
    &&& forall|n:usize| s::registered(a,n) ==> (h.episode)(n) <= h.time
        && (a.control.fibers[n].phase != Phase::Inactive ==> (h.episode)(n) > 0)
    &&& forall|child:usize| h.births.dom().contains(child) ==> {
        let b = h.births[child];
        &&& s::registered(a,child) && a.control.fibers[child].parent == Some(b.parent)
        &&& kind(b.inverse) == Some(child)
        &&& b.episode > 0 && b.episode <= b.landed_at && b.landed_at <= h.time
        &&& (!a.control.fibers[child].retired ==> {
            &&& s::registered(a,b.parent) && a.control.fibers[b.parent].phase != Phase::Inactive
            &&& b.episode == (h.episode)(b.parent)
            &&& a.accumulators[b.parent].contains(b.inverse)
        })
    }
}

/// Monotonicity is a property of primitive table writes and O-Retire, derived
/// before composing them into the complete accumulator.
pub open spec fn recovery_frame<V>(a:s::State<V>,z:s::State<V>) -> bool {
    &&& a.control.fibers.dom() == z.control.fibers.dom()
    &&& a.accumulators == z.accumulators
    &&& forall|n:usize| s::registered(a,n) ==> {
        &&& c::interface_same(a.control.fibers[n],z.control.fibers[n])
        &&& a.control.fibers[n].phase == z.control.fibers[n].phase
        &&& (a.control.fibers[n].retired ==> z.control.fibers[n].retired)
    }
}

pub proof fn inverse_frame<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,a:s::State<V>,n:usize,token:nat)
    requires inverse(model,kind,a,n,token),
    ensures recovery_frame(a,(model.undo)(token,a)),
        kind(token).is_some() ==> s::registered((model.undo)(token,a),kind(token).unwrap())
            && (model.undo)(token,a).control.fibers[kind(token).unwrap()].retired,
{
    let z = (model.undo)(token,a);
    if let Some(child) = kind(token) {
        assert forall|m:usize| s::registered(a,m) implies {
            &&& c::interface_same(a.control.fibers[m],z.control.fibers[m])
            &&& a.control.fibers[m].phase == z.control.fibers[m].phase
            &&& (a.control.fibers[m].retired ==> z.control.fibers[m].retired)
        } by { if m != child { assert(a.control.fibers[m] == z.control.fibers[m]); } }
        assert(a.control.fibers.dom() =~= z.control.fibers.dom()) by {
            assert forall|m:usize| a.control.fibers.dom().contains(m) == z.control.fibers.dom().contains(m) by {
                if m != child {
                    assert(c::frame(a.control,z.control,child));
                    assert(c::registered(a.control,m) == c::registered(z.control,m));
                } else {
                    assert(c::registered(a.control,child));
                    assert(c::registered(z.control,child));
                }
            }
        }
    }
}

pub proof fn recovery_consequences<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,tokens:Seq<nat>,a:s::State<V>,n:usize)
    requires recovery(model,kind,tokens,a,n),
    ensures recovery_frame(a,s::restore(model,tokens,a)),
        forall|token:nat,child:usize| tokens.contains(token) && kind(token) == Some(child)
            ==> s::registered(s::restore(model,tokens,a),child)
                && s::restore(model,tokens,a).control.fibers[child].retired,
    decreases tokens.len(),
{
    if tokens.len() > 0 {
        let b = (model.undo)(tokens.last(),a);
        let z = s::restore(model,tokens,a);
        inverse_frame(model,kind,a,n,tokens.last());
        recovery_consequences(model,kind,tokens.drop_last(),b,n);
        assert forall|m:usize| s::registered(a,m) implies {
            &&& c::interface_same(a.control.fibers[m],z.control.fibers[m])
            &&& a.control.fibers[m].phase == z.control.fibers[m].phase
            &&& (a.control.fibers[m].retired ==> z.control.fibers[m].retired)
        } by { assert(s::registered(b,m)); }
        assert forall|token:nat,child:usize| tokens.contains(token) && kind(token) == Some(child) implies
            s::registered(z,child) && z.control.fibers[child].retired by {
            if token == tokens.last() { assert(s::registered(b,child)); }
            else {
                let i = choose|i:int| 0 <= i < tokens.len() && tokens[i] == token;
                assert(i < tokens.len()-1);
                assert(tokens.drop_last()[i] == token);
                assert(tokens.drop_last().contains(token));
            }
        }
    }
}

pub proof fn recovery_retires_token<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,tokens:Seq<nat>,a:s::State<V>,n:usize,token:nat,child:usize)
    requires recovery(model,kind,tokens,a,n),tokens.contains(token),kind(token) == Some(child),
    ensures s::registered(s::restore(model,tokens,a),child),s::restore(model,tokens,a).control.fibers[child].retired,
{
    recovery_consequences(model,kind,tokens,a,n);
}

pub proof fn initial_valid<V>(kind:spec_fn(nat)->Option<usize>)
    ensures valid(kind,initial(),p::empty::<V>()),
{ }

/// Every actual rule extends the trace-derived history. In particular L-Unload
/// retires each live child by finding its creation token in the real accumulator.
pub proof fn step_preserves_history<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,h:History,a:s::State<V>,z:s::State<V>,n:usize,rule:c::Rule)
    requires p::well_formed(a),valid(kind,h,a),s::step(model,a,z,n,rule),admissible(model,kind,a,z,n,rule),
    ensures p::well_formed(z),valid(kind,advance(model,kind,h,a,z,n,rule),z),
{
    p::full_preservation(model,a,z,n,rule);
    let hz = advance(model,kind,h,a,z,n,rule);
    let y = (model.iterate)(n,a.iterators[n].unwrap(),a);
    let born = if landing(model,a,z,n,rule) { kind(y.inverse) } else { None };
    if landing(model,a,z,n,rule) {
        assert(z.accumulators[n] == a.accumulators[n].push(y.inverse));
        assert(z.control.fibers[n].phase != Phase::Inactive);
        if let Some(child) = born {
            assert(p::child_map(a,y.state,n,child));
            assert(child != n);
            assert(!s::registered(a,child));
            assert(s::registered(z,child));
            assert(z.control.fibers[child].phase == Phase::Inactive);
        } else { assert(p::table_map(a,y.state,n)); }
    }
    if rule == c::Rule::Unload {
        recovery_consequences(model,kind,a.accumulators[n],a,n);
    }
    assert forall|m:usize| s::registered(z,m) implies (hz.episode)(m) <= hz.time
        && (z.control.fibers[m].phase != Phase::Inactive ==> (hz.episode)(m) > 0) by {
        if born == Some(m) {
            assert(z.control.fibers[m].phase == Phase::Inactive);
        } else if m == n {
            match rule {
                c::Rule::Insert => {},
                c::Rule::Remove => {},
                c::Rule::Begin => {},
                c::Rule::Unload => {},
                _ => {
                    assert(s::registered(a,m));
                    assert(a.control.fibers[m].phase != Phase::Inactive || z.control.fibers[m].phase == Phase::Inactive);
                },
            }
        } else {
            match rule {
                c::Rule::Insert | c::Rule::Remove | c::Rule::Retire => {
                    assert(c::frame(a.control,z.control,n));
                },
                c::Rule::Iter | c::Rule::Finish | c::Rule::Divert => {
                    if landing(model,a,z,n,rule) {
                        if let Some(child) = born { assert(c::frame(a.control,y.state.control,child)); }
                    }
                },
                _ => {},
            }
            assert(s::registered(a,m));
            assert(a.control.fibers[m].phase == z.control.fibers[m].phase);
        }
    }
    assert forall|child:usize| hz.births.dom().contains(child) implies {
        let b = hz.births[child];
        &&& s::registered(z,child) && z.control.fibers[child].parent == Some(b.parent)
        &&& kind(b.inverse) == Some(child)
        &&& b.episode > 0 && b.episode <= b.landed_at && b.landed_at <= hz.time
        &&& (!z.control.fibers[child].retired ==> {
            &&& s::registered(z,b.parent) && z.control.fibers[b.parent].phase != Phase::Inactive
            &&& b.episode == (hz.episode)(b.parent)
            &&& z.accumulators[b.parent].contains(b.inverse)
        })
    } by {
        let b = hz.births[child];
        if born == Some(child) {
            assert(b.parent == n);
            assert(b.episode == (h.episode)(n));
            assert(s::registered(a,n));
            assert(a.control.fibers[n].phase == Phase::Loading);
            assert(z.accumulators[n][a.accumulators[n].len() as int] == y.inverse);
            assert(z.accumulators[n].contains(y.inverse));
        } else {
            assert(h.births.dom().contains(child));
            assert(b == h.births[child]);
            assert(s::registered(a,child));
            match rule {
                c::Rule::Insert | c::Rule::Remove | c::Rule::Retire => {
                    assert(c::frame(a.control,z.control,n));
                    if child != n { assert(a.control.fibers[child] == z.control.fibers[child]); }
                },
                c::Rule::Iter | c::Rule::Finish | c::Rule::Divert => {
                    if landing(model,a,z,n,rule) {
                        if let Some(fresh) = born {
                            assert(c::frame(a.control,y.state.control,fresh));
                            assert(child != fresh);
                        }
                    }
                },
                _ => {},
            }
            assert(s::registered(z,child));
            assert(z.control.fibers[child].parent == Some(b.parent));
            assert(a.control.fibers[child].retired ==> z.control.fibers[child].retired);
            if !z.control.fibers[child].retired {
                assert(!a.control.fibers[child].retired);
                assert(s::registered(a,b.parent));
                assert(a.control.fibers[b.parent].phase != Phase::Inactive);
                assert(a.accumulators[b.parent].contains(b.inverse));
                if rule == c::Rule::Unload && b.parent == n {
                    let restored = s::restore(model,a.accumulators[n],a);
                    assert(kind(b.inverse) == Some(child));
                    assert(a.accumulators[n].contains(b.inverse));
                    recovery_retires_token(model,kind,a.accumulators[n],a,n,b.inverse,child);
                    assert(restored.control.fibers[child].retired);
                    assert(z.control.fibers[child].retired);
                }
                assert(!(rule == c::Rule::Begin && b.parent == n));
                assert(!(rule == c::Rule::Insert && b.parent == n));
                assert(!(rule == c::Rule::Remove && b.parent == n));
                if landing(model,a,z,n,rule) {
                    if let Some(fresh) = born {
                        assert(b.parent != fresh);
                        assert(c::frame(a.control,y.state.control,fresh));
                    }
                    if b.parent == n {
                        let i = choose|i:int| 0 <= i < a.accumulators[n].len() && a.accumulators[n][i] == b.inverse;
                        assert(z.accumulators[n][i] == b.inverse);
                    } else {
                        assert(z.accumulators[b.parent] == a.accumulators[b.parent]);
                    }
                }
                assert(s::registered(z,b.parent));
                assert(z.control.fibers[b.parent].phase != Phase::Inactive);
                assert((hz.episode)(b.parent) == (h.episode)(b.parent));
                assert(z.accumulators[b.parent].contains(b.inverse));
            }
        }
    }
}

/// An Inactive-to-Loading transition starts a strictly new episode. Every
/// surviving child from an earlier episode of that creator is already retired;
/// equality of committed dependency views therefore cannot conflate episodes.
pub proof fn begin_separates_generations<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,h:History,a:s::State<V>,z:s::State<V>,n:usize)
    requires valid(kind,h,a),s::step(model,a,z,n,c::Rule::Begin),
    ensures (advance(model,kind,h,a,z,n,c::Rule::Begin).episode)(n) > (h.episode)(n),
        forall|child:usize| h.births.dom().contains(child) && h.births[child].parent == n
            ==> a.control.fibers[child].retired,
{
    assert(s::registered(a,n));
    assert forall|child:usize| h.births.dom().contains(child) && h.births[child].parent == n
        implies a.control.fibers[child].retired by {
        if !a.control.fibers[child].retired { assert(a.control.fibers[n].phase != Phase::Inactive); }
    }
}

/// The history is reconstructed from the state/label trace; there is no caller
/// supplied provenance sequence and no intermediate-state invariant premise.
pub open spec fn execution<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>) -> bool {
    &&& states.len() == labels.len()+1
    &&& states.first() == p::empty::<V>()
    &&& forall|i:int| 0 <= i < labels.len() ==> s::step(model,states[i],states[i+1],labels[i].0,labels[i].1)
        && admissible(model,kind,states[i],states[i+1],labels[i].0,labels[i].1)
}

pub open spec fn history<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>) -> History
    decreases labels.len(),
{
    if labels.len() == 0 { initial() }
    else {
        let i = labels.len()-1;
        advance(model,kind,history(model,kind,states.drop_last(),labels.drop_last()),
            states[i],states[i+1],labels[i].0,labels[i].1)
    }
}

pub proof fn execution_history<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>)
    requires execution(model,kind,states,labels),
    ensures p::well_formed(states.last()),valid(kind,history(model,kind,states,labels),states.last()),
        history(model,kind,states,labels).time == labels.len(),
    decreases labels.len(),
{
    if labels.len() == 0 {
        p::empty_well_formed::<V>();
        initial_valid::<V>(kind);
        assert(states.last() == states.first());
    } else {
        let previous = states.drop_last();
        let earlier = labels.drop_last();
        assert(execution(model,kind,previous,earlier)) by {
            assert forall|i:int| 0 <= i < earlier.len() implies
                s::step(model,previous[i],previous[i+1],earlier[i].0,earlier[i].1)
                    && admissible(model,kind,previous[i],previous[i+1],earlier[i].0,earlier[i].1) by {}
        }
        execution_history(model,kind,previous,earlier);
        let i = labels.len()-1;
        assert(previous.last() == states[i]);
        step_preserves_history(model,kind,history(model,kind,previous,earlier),states[i],states[i+1],labels[i].0,labels[i].1);
    }
}

/// A record points to an actual labelled landing, including its exact returned
/// inverse. A registry parent alone never suffices to manufacture this evidence.
pub open spec fn actual_birth<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>,child:usize,b:Birth) -> bool {
    &&& 0 < b.landed_at <= labels.len()
    &&& {
        let i = b.landed_at as int - 1;
        let a = states[i];
        let z = states[i+1];
        let n = labels[i].0;
        let rule = labels[i].1;
        let y = (model.iterate)(n,a.iterators[n].unwrap(),a);
        &&& n == b.parent
        &&& landing(model,a,z,n,rule)
        &&& b.inverse == y.inverse && kind(y.inverse) == Some(child)
        &&& p::child_map(a,y.state,n,child)
    }
}

pub proof fn birth_records_are_landings<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>)
    requires execution(model,kind,states,labels),
    ensures forall|child:usize| history(model,kind,states,labels).births.dom().contains(child)
        ==> actual_birth(model,kind,states,labels,child,history(model,kind,states,labels).births[child]),
    decreases labels.len(),
{
    if labels.len() > 0 {
        let previous = states.drop_last();
        let earlier = labels.drop_last();
        assert(execution(model,kind,previous,earlier)) by {
            assert forall|i:int| 0 <= i < earlier.len() implies
                s::step(model,previous[i],previous[i+1],earlier[i].0,earlier[i].1)
                    && admissible(model,kind,previous[i],previous[i+1],earlier[i].0,earlier[i].1) by {}
        }
        execution_history(model,kind,previous,earlier);
        birth_records_are_landings(model,kind,previous,earlier);
        let old = history(model,kind,previous,earlier);
        let h = history(model,kind,states,labels);
        let i = labels.len()-1;
        let n = labels[i].0;
        let rule = labels[i].1;
        let y = (model.iterate)(n,states[i].iterators[n].unwrap(),states[i]);
        assert forall|child:usize| h.births.dom().contains(child) implies
            actual_birth(model,kind,states,labels,child,h.births[child]) by {
            let b = h.births[child];
            if landing(model,states[i],states[i+1],n,rule) && kind(y.inverse) == Some(child) {
                assert(b.landed_at == labels.len());
                assert(p::child_map(states[i],y.state,n,child));
            } else {
                assert(old.births.dom().contains(child));
                assert(b == old.births[child]);
                assert(actual_birth(model,kind,previous,earlier,child,b));
                let j = b.landed_at as int - 1;
                assert(earlier[j] == labels[j]);
                assert(previous[j] == states[j]);
                assert(previous[j+1] == states[j+1]);
            }
        }
    }
}

pub open spec fn born_retirement_closed<V>(h:History,a:s::State<V>) -> bool {
    forall|child:usize| h.births.dom().contains(child)
        && a.control.fibers[h.births[child].parent].phase == Phase::Inactive
        ==> a.control.fibers[child].retired
}

pub proof fn creation_history_closure<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>)
    requires execution(model,kind,states,labels),
    ensures born_retirement_closed(history(model,kind,states,labels),states.last()),
{
    execution_history(model,kind,states,labels);
}

/// The original nine rules also allow external children. The following is an
/// explicit stronger orchestration profile, not a reinterpretation of Insert.
pub open spec fn external_roots<V>(states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>) -> bool {
    forall|i:int| 0 <= i < labels.len() && labels[i].1 == c::Rule::Insert
        ==> states[i+1].control.fibers[labels[i].0].parent.is_none()
}

pub open spec fn all_children_born<V>(h:History,a:s::State<V>) -> bool {
    forall|child:usize| s::registered(a,child) && a.control.fibers[child].parent.is_some()
        ==> h.births.dom().contains(child)
}

pub proof fn step_covers_children<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,h:History,a:s::State<V>,z:s::State<V>,n:usize,rule:c::Rule)
    requires p::well_formed(a),valid(kind,h,a),all_children_born(h,a),
        s::step(model,a,z,n,rule),admissible(model,kind,a,z,n,rule),
        rule == c::Rule::Insert ==> z.control.fibers[n].parent.is_none(),
    ensures all_children_born(advance(model,kind,h,a,z,n,rule),z),
{
    let hz = advance(model,kind,h,a,z,n,rule);
    let y = (model.iterate)(n,a.iterators[n].unwrap(),a);
    if rule == c::Rule::Unload { recovery_consequences(model,kind,a.accumulators[n],a,n); }
    assert forall|child:usize| s::registered(z,child) && z.control.fibers[child].parent.is_some() implies
        hz.births.dom().contains(child) by {
        if landing(model,a,z,n,rule) {
            if let Some(fresh) = kind(y.inverse) {
                assert(p::child_map(a,y.state,n,fresh));
                if fresh != child { assert(c::frame(a.control,y.state.control,fresh)); }
            }
        }
        if !hz.births.dom().contains(child) {
            match rule {
                c::Rule::Insert | c::Rule::Retire | c::Rule::Remove => {
                    assert(c::frame(a.control,z.control,n));
                },
                _ => {},
            }
            assert(s::registered(a,child));
            assert(a.control.fibers[child].parent.is_some());
            assert(h.births.dom().contains(child));
        }
    }
}

pub proof fn root_profile_covers_children<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>)
    requires execution(model,kind,states,labels),external_roots(states,labels),
    ensures all_children_born(history(model,kind,states,labels),states.last()),
    decreases labels.len(),
{
    if labels.len() == 0 { assert(states.last() == p::empty::<V>()); }
    else {
        let previous = states.drop_last();
        let earlier = labels.drop_last();
        assert(execution(model,kind,previous,earlier)) by {
            assert forall|i:int| 0 <= i < earlier.len() implies
                s::step(model,previous[i],previous[i+1],earlier[i].0,earlier[i].1)
                    && admissible(model,kind,previous[i],previous[i+1],earlier[i].0,earlier[i].1) by {}
        }
        assert(external_roots(previous,earlier));
        execution_history(model,kind,previous,earlier);
        root_profile_covers_children(model,kind,previous,earlier);
        let i = labels.len()-1;
        assert(previous.last() == states[i]);
        step_covers_children(model,kind,history(model,kind,previous,earlier),states[i],states[i+1],labels[i].0,labels[i].1);
    }
}

/// Corrected Lemma 77: support is derived from actual births and accumulator
/// recovery, with total provision only used to connect full and control target.
pub proof fn quiet_support_from_creation_history<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>)
    requires execution(model,kind,states,labels),
        all_children_born(history(model,kind,states,labels),states.last()),
        s::quiet(states.last()),s::total_active(states.last()),
    ensures global::retirement_closed(states.last().control),
        global::support_solution(states.last().control,global::active(states.last().control)),
{
    execution_history(model,kind,states,labels);
    creation_history_closure(model,kind,states,labels);
    let a = states.last();
    let h = history(model,kind,states,labels);
    assert forall|child:usize,parent:usize| c::registered(a.control,child)
        && a.control.fibers[child].parent == Some(parent)
        && a.control.fibers[parent].phase == Phase::Inactive implies a.control.fibers[child].retired by {
        assert(s::registered(a,child));
        assert(a.control.fibers[child].parent.is_some());
        assert(h.births.dom().contains(child));
        assert(h.births[child].parent == parent);
    }
    s::quiet_total_agrees(a);
    global::quiet_active_support(a.control);
}

pub proof fn root_profile_quiet_support<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>)
    requires execution(model,kind,states,labels),external_roots(states,labels),
        s::quiet(states.last()),s::total_active(states.last()),
    ensures global::support_solution(states.last().control,global::active(states.last().control)),
{
    root_profile_covers_children(model,kind,states,labels);
    quiet_support_from_creation_history(model,kind,states,labels);
}

/// Origin-aware corrected support: an external Insert's parent records
/// ownership only. A lifecycle-created fiber additionally requires its creator
/// to be selected. This preserves the original general Insert capability.
pub open spec fn origin_support_clause(h:History,a:c::State,selected:ISet<usize>,n:usize) -> bool {
    &&& c::registered(a,n) && !a.fibers[n].retired
    &&& (h.births.dom().contains(n) ==> selected.contains(h.births[n].parent))
    &&& forall|key:crate::Port| a.fibers[n].dependencies.contains(key) ==> global::provided_by(a,selected,key)
}

pub open spec fn origin_support_solution(h:History,a:c::State,selected:ISet<usize>) -> bool {
    forall|n:usize| selected.contains(n) == origin_support_clause(h,a,selected,n)
}

/// The support equation follows for unrestricted external Insert, using the
/// history-derived creator obligation only where an actual child inverse exists.
pub proof fn quiet_origin_support<V>(kind:spec_fn(nat)->Option<usize>,h:History,a:s::State<V>)
    requires p::well_formed(a),valid(kind,h,a),s::quiet(a),s::total_active(a),
    ensures origin_support_solution(h,a.control,global::active(a.control)),
{
    s::quiet_total_agrees(a);
    assert forall|n:usize| global::active(a.control).contains(n)
        == origin_support_clause(h,a.control,global::active(a.control),n) by {
        if c::registered(a.control,n) {
            global::target_iff_available(a.control,n);
            assert(global::active(a.control).contains(n)
                == (exists|view:ISet<crate::Binding>| c::target(a.control,n,view)));
            if global::active(a.control).contains(n) && h.births.dom().contains(n) {
                assert(s::registered(a,n));
                assert(!a.control.fibers[n].retired);
                let parent = h.births[n].parent;
                assert(s::registered(a,parent));
                assert(a.control.fibers[parent].phase != Phase::Inactive);
                assert(global::active(a.control).contains(parent));
            }
            assert forall|key:crate::Port| a.control.fibers[n].dependencies.contains(key) implies
                ((exists|m:usize| c::publishes(a.control,key,m))
                    == global::provided_by(a.control,global::active(a.control),key)) by {
                if exists|m:usize| c::publishes(a.control,key,m) {
                    let m = choose|m:usize| c::publishes(a.control,key,m);
                    assert(global::active(a.control).contains(m));
                    assert(global::provided_by(a.control,global::active(a.control),key));
                }
                if global::provided_by(a.control,global::active(a.control),key) {
                    let m = choose|m:usize| global::active(a.control).contains(m) && c::registered(a.control,m)
                        && a.control.fibers[m].provisions.contains(key);
                    assert(c::publishes(a.control,key,m));
                }
            }
            if origin_support_clause(h,a.control,global::active(a.control),n) {
                assert forall|key:crate::Port| a.control.fibers[n].dependencies.contains(key) implies
                    exists|m:usize| c::publishes(a.control,key,m) by {
                    assert(global::provided_by(a.control,global::active(a.control),key));
                }
                assert(global::active(a.control).contains(n));
            }
        }
    }
}

pub proof fn execution_quiet_origin_support<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>)
    requires execution(model,kind,states,labels),s::quiet(states.last()),s::total_active(states.last()),
    ensures origin_support_solution(history(model,kind,states,labels),states.last().control,global::active(states.last().control)),
{
    execution_history(model,kind,states,labels);
    quiet_origin_support(kind,history(model,kind,states,labels),states.last());
}

/// A strict retirement inverse has a real domain condition: every referenced
/// child must still be registered before the accumulator starts.
pub proof fn recovery_requires_children<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,tokens:Seq<nat>,a:s::State<V>,n:usize)
    requires recovery(model,kind,tokens,a,n),
    ensures forall|token:nat,child:usize| tokens.contains(token) && kind(token) == Some(child) ==> s::registered(a,child),
{
    recovery_consequences(model,kind,tokens,a,n);
    assert forall|token:nat,child:usize| tokens.contains(token) && kind(token) == Some(child) implies s::registered(a,child) by {
        recovery_retires_token(model,kind,tokens,a,n,token,child);
    }
}


/// Every child reference in every actual accumulator is retained, even after
/// that child is retired. Birth metadata and retirement bits are not a proxy
/// for this domain obligation.
pub open spec fn retained<V>(kind:spec_fn(nat)->Option<usize>,a:s::State<V>) -> bool {
    forall|owner:usize,token:nat,child:usize| s::registered(a,owner)
        && a.accumulators[owner].contains(token) && kind(token) == Some(child)
        ==> s::registered(a,child)
}

pub open spec fn remove_unreferenced<V>(kind:spec_fn(nat)->Option<usize>,a:s::State<V>,child:usize) -> bool {
    forall|owner:usize,token:nat| s::registered(a,owner) && a.accumulators[owner].contains(token)
        ==> kind(token) != Some(child)
}

/// Table inverses carry their ordinary local typing obligation. Child inverses
/// have a concrete interpreter, so their retirement behavior is proved below.
pub open spec fn primitive_inverses<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>) -> bool {
    &&& forall|a:s::State<V>,owner:usize,token:nat| p::well_formed(a) && s::registered(a,owner)
        && a.accumulators[owner].contains(token) && kind(token).is_none()
        ==> p::table_map(a,(model.undo)(token,a),owner)
    &&& forall|a:s::State<V>,token:nat,child:usize| kind(token) == Some(child) && #[trigger] s::registered(a,child)
        ==> #[trigger] (model.undo)(token,a) == s::with_control(a,global::retire_fiber(a.control,child))
}

pub proof fn concrete_child_retirement<V>(a:s::State<V>,child:usize)
    requires s::registered(a,child),
    ensures s::child_retire(a,s::with_control(a,global::retire_fiber(a.control,child)),child),
{
    let z = s::with_control(a,global::retire_fiber(a.control,child));
    assert(c::frame(a.control,z.control,child));
}

pub proof fn retained_inverse<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,a:s::State<V>,owner:usize,token:nat)
    requires primitive_inverses(model,kind),p::well_formed(a),retained(kind,a),s::registered(a,owner),
        a.accumulators[owner].contains(token),
    ensures inverse(model,kind,a,owner,token),
{
    if let Some(child) = kind(token) {
        assert(s::registered(a,child));
        concrete_child_retirement(a,child);
    }
}

pub proof fn recovery_is_admissible<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,tokens:Seq<nat>,a:s::State<V>,owner:usize)
    requires recovery(model,kind,tokens,a,owner),
    ensures p::admissible_restore(model,tokens,a,owner),
    decreases tokens.len(),
{
    if tokens.len() > 0 {
        let b = (model.undo)(tokens.last(),a);
        if let Some(child) = kind(tokens.last()) { assert(s::child_retire(a,b,child)); }
        assert(p::inverse_map(a,b,owner));
        recovery_is_admissible(model,kind,tokens.drop_last(),b,owner);
    }
}

/// Running one inverse keeps the registry and all accumulators fixed. Thus the
/// domain check for later LIFO positions follows from retention at entry.
pub proof fn retained_recovery<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,tokens:Seq<nat>,a:s::State<V>,owner:usize)
    requires primitive_inverses(model,kind),p::well_formed(a),retained(kind,a),s::registered(a,owner),
        forall|token:nat| tokens.contains(token) ==> a.accumulators[owner].contains(token),
    ensures recovery(model,kind,tokens,a,owner),p::admissible_restore(model,tokens,a,owner),
    decreases tokens.len(),
{
    if tokens.len() > 0 {
        assert(tokens.contains(tokens.last()));
        retained_inverse(model,kind,a,owner,tokens.last());
        let b = (model.undo)(tokens.last(),a);
        inverse_frame(model,kind,a,owner,tokens.last());
        if let Some(child) = kind(tokens.last()) { assert(s::child_retire(a,b,child)); }
        assert(p::inverse_map(a,b,owner));
        p::inverse_preservation(a,b,owner);
        assert(retained(kind,b)) by {
            assert forall|n:usize,token:nat,child:usize| s::registered(b,n)
                && b.accumulators[n].contains(token) && kind(token) == Some(child)
                implies s::registered(b,child) by {
                assert(s::registered(a,n));
                assert(a.accumulators[n].contains(token));
                assert(s::registered(a,child));
            }
        }
        assert forall|token:nat| tokens.drop_last().contains(token) implies b.accumulators[owner].contains(token) by {
            let i = choose|i:int| 0 <= i < tokens.drop_last().len() && tokens.drop_last()[i] == token;
            assert(tokens[i] == token);
            assert(tokens.contains(token));
        }
        retained_recovery(model,kind,tokens.drop_last(),b,owner);
    }
    recovery_is_admissible(model,kind,tokens,a,owner);
}

pub proof fn step_preserves_retention<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,a:s::State<V>,z:s::State<V>,n:usize,rule:c::Rule)
    requires p::well_formed(a),retained(kind,a),s::step(model,a,z,n,rule),admissible(model,kind,a,z,n,rule),
        rule == c::Rule::Remove ==> remove_unreferenced(kind,a,n),
    ensures retained(kind,z),
{
    let y = (model.iterate)(n,a.iterators[n].unwrap(),a);
    let born = if landing(model,a,z,n,rule) { kind(y.inverse) } else { None };
    if rule == c::Rule::Unload { recovery_consequences(model,kind,a.accumulators[n],a,n); }
    if landing(model,a,z,n,rule) {
        if let Some(child) = born {
            assert(p::child_map(a,y.state,n,child));
            assert(child != n);
            assert(z.accumulators[child].len() == 0);
        }
    }
    assert forall|owner:usize,token:nat,child:usize| s::registered(z,owner)
        && z.accumulators[owner].contains(token) && kind(token) == Some(child) implies s::registered(z,child) by {
        if born == Some(owner) { assert(z.accumulators[owner].len() == 0); }
        else if owner == n && (rule == c::Rule::Insert || rule == c::Rule::Begin || rule == c::Rule::Unload) {
            assert(z.accumulators[owner].len() == 0);
        } else {
            match rule {
                c::Rule::Insert | c::Rule::Retire | c::Rule::Remove => { assert(c::frame(a.control,z.control,n)); },
                _ => {},
            }
            if landing(model,a,z,n,rule) {
                if let Some(fresh) = born { assert(c::frame(a.control,y.state.control,fresh)); }
            }
            assert(s::registered(a,owner));
            if owner == n && landing(model,a,z,n,rule) && token == y.inverse {
                assert(born == Some(child));
                assert(s::registered(z,child));
            } else {
                if owner == n && landing(model,a,z,n,rule) {
                    let i = choose|i:int| 0 <= i < z.accumulators[owner].len() && z.accumulators[owner][i] == token;
                    assert(i < a.accumulators[owner].len());
                    assert(a.accumulators[owner][i] == token);
                } else { assert(z.accumulators[owner] == a.accumulators[owner]); }
                assert(a.accumulators[owner].contains(token));
                assert(s::registered(a,child));
                if rule == c::Rule::Remove { assert(child != n); }
                assert(s::registered(z,child));
            }
        }
    }
}

/// A corrected removal policy plus primitive typing. Unload has no caller
/// supplied recovery contract: retention must establish it inductively.
pub open spec fn retention_protocol<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>) -> bool {
    &&& states.len() == labels.len()+1 && states.first() == p::empty::<V>()
    &&& forall|i:int| 0 <= i < labels.len() ==> {
        let (n,rule) = #[trigger] labels[i];
        &&& s::step(model,states[i],states[i+1],n,rule)
        &&& (rule != c::Rule::Unload ==> admissible(model,kind,states[i],states[i+1],n,rule))
        &&& (rule == c::Rule::Remove ==> remove_unreferenced(kind,states[i],n))
    }
}

pub proof fn retention_protocol_refines<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>)
    requires primitive_inverses(model,kind),retention_protocol(model,kind,states,labels),
    ensures execution(model,kind,states,labels),retained(kind,states.last()),p::well_formed(states.last()),
    decreases labels.len(),
{
    if labels.len() == 0 {
        assert(states.last() == p::empty::<V>());
        p::empty_well_formed::<V>();
    } else {
        let previous = states.drop_last();
        let earlier = labels.drop_last();
        assert(retention_protocol(model,kind,previous,earlier)) by {
            assert forall|i:int| 0 <= i < earlier.len() implies {
                let (n,rule) = #[trigger] earlier[i];
                &&& s::step(model,previous[i],previous[i+1],n,rule)
                &&& (rule != c::Rule::Unload ==> admissible(model,kind,previous[i],previous[i+1],n,rule))
                &&& (rule == c::Rule::Remove ==> remove_unreferenced(kind,previous[i],n))
            } by {}
        }
        retention_protocol_refines(model,kind,previous,earlier);
        let i = labels.len()-1;
        let a = states[i];
        let z = states[i+1];
        let (n,rule) = labels[i];
        assert(previous.last() == a);
        if rule == c::Rule::Unload {
            retained_recovery(model,kind,a.accumulators[n],a,n);
            assert(admissible(model,kind,a,z,n,rule));
        }
        step_preserves_retention(model,kind,a,z,n,rule);
        p::full_preservation(model,a,z,n,rule);
        assert(execution(model,kind,states,labels)) by {
            assert forall|j:int| 0 <= j < labels.len() implies
                s::step(model,states[j],states[j+1],labels[j].0,labels[j].1)
                    && admissible(model,kind,states[j],states[j+1],labels[j].0,labels[j].1) by {
                if j < earlier.len() { assert(earlier[j] == labels[j]); assert(previous[j+1] == states[j+1]); }
            }
        }
    }
}

pub proof fn retained_protocol_quiet_support<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>)
    requires primitive_inverses(model,kind),retention_protocol(model,kind,states,labels),
        s::quiet(states.last()),s::total_active(states.last()),
    ensures origin_support_solution(history(model,kind,states,labels),states.last().control,global::active(states.last().control)),
{
    retention_protocol_refines(model,kind,states,labels);
    execution_quiet_origin_support(model,kind,states,labels);
}

pub open spec fn creation_token_kind(token:nat) -> Option<usize> {
    if token == 1 { Some(1usize) } else { None }
}

/// The paper witness's actual child interpreter satisfies the primitive law;
/// this is not merely an uninterpreted model satisfying a global assumption.
pub proof fn creation_model_primitive_inverses()
    ensures primitive_inverses(crate::paper_counterexamples::creation_model(),|token:nat| creation_token_kind(token)),
{
    let model = crate::paper_counterexamples::creation_model();
    assert forall|a:s::State<u64>,owner:usize,token:nat| p::well_formed(a) && s::registered(a,owner)
        && a.accumulators[owner].contains(token) && creation_token_kind(token).is_none()
        implies p::table_map(a,(model.undo)(token,a),owner) by {
        assert(token != 1);
        assert((model.undo)(token,a) == a);
    }
    assert forall|a:s::State<u64>,token:nat,child:usize| creation_token_kind(token) == Some(child)
        && #[trigger] s::registered(a,child) implies #[trigger] (model.undo)(token,a)
            == s::with_control(a,global::retire_fiber(a.control,child)) by {}
}

/// Retired does not mean unreferenced: the original Remove rule can delete this
/// inactive child while its creator still holds the child-retirement inverse.
/// The corrected gate detects precisely that dangling-reference case.
pub proof fn retired_child_removal_still_needs_retention()
    ensures {
        let a = crate::paper_counterexamples::creator_finished();
        let b = s::with_control(a,global::retire_fiber(a.control,1));
        let model = crate::paper_counterexamples::creation_model();
        let kind:spec_fn(nat)->Option<usize> = |token:nat| creation_token_kind(token);
        &&& s::child_retire(a,b,1)
        &&& b.control.fibers[1usize].retired && b.control.fibers[1usize].phase == Phase::Inactive
        &&& retained(kind,b)
        &&& s::step(model,b,s::erase(b,1),1,c::Rule::Remove)
        &&& !remove_unreferenced(kind,b,1)
        &&& !retained(kind,s::erase(b,1))
    },
{
    crate::paper_counterexamples::transposition_parent_counterexample();
    let a = crate::paper_counterexamples::creator_finished();
    let b = s::with_control(a,global::retire_fiber(a.control,1));
    let model = crate::paper_counterexamples::creation_model();
    let kind:spec_fn(nat)->Option<usize> = |token:nat| creation_token_kind(token);
    concrete_child_retirement(a,1);
    assert forall|owner:usize,token:nat,child:usize| s::registered(b,owner)
        && b.accumulators[owner].contains(token) && kind(token) == Some(child) implies s::registered(b,child) by {
        assert(owner == 0 || owner == 1);
        assert(child == 1);
    }
    assert forall|m:usize| s::registered(b,m) implies b.control.fibers[m].parent != Some(1usize) by {
        assert(m == 0 || m == 1);
    }
    assert(b.accumulators[0usize][0] == 1nat);
    assert(b.accumulators[0usize].contains(1nat));
    assert(s::registered(b,0));
    assert(kind(1) == Some(1usize));
    assert(c::frame(b.control,s::erase(b,1).control,1));
    assert(s::erase(b,1).accumulators[0usize].contains(1nat));
    assert(s::registered(s::erase(b,1),0));
    assert(!s::registered(s::erase(b,1),1));
}

pub open spec fn external_child_model() -> s::Model<u64> {
    s::Model { iterate:|_actor:usize,_iterator:nat,a:s::State<u64>| s::Yield {state:a,inverse:0,next:None},
        undo:|_token:nat,a:s::State<u64>| a }
}

pub open spec fn external_child_states() -> Seq<s::State<u64>> {
    let a0 = p::empty::<u64>();
    let a1 = s::extend_child(a0,global::insert_fiber(a0.control,0,None,ISet::empty(),ISet::empty()),0,0);
    let a2 = s::with_control(a1,global::retire_fiber(a1.control,0));
    let a3 = s::extend_child(a2,global::insert_fiber(a2.control,1,Some(0),ISet::empty(),ISet::empty()),1,0);
    let a4 = s::edit(a3,1,Phase::Loading,ISet::empty(),Some(0),Seq::empty());
    let a5 = s::edit(a4,1,Phase::Active,ISet::empty(),None,seq![0nat]);
    seq![a0,a1,a2,a3,a4,a5]
}

pub open spec fn external_child_labels() -> Seq<(usize,c::Rule)> {
    seq![(0usize,c::Rule::Insert),(0usize,c::Rule::Retire),(1usize,c::Rule::Insert),
        (1usize,c::Rule::Begin),(1usize,c::Rule::Finish)]
}

/// Printed Lemma 77 fails for a permitted external non-root Insert. The parent
/// is inactive and retired, but the child has no coeffect dependency on it.
/// All five steps are full rules, the context is quiet and total, and both
/// provider and parent precedence have a finite acyclic ranking.
pub proof fn external_parent_support_counterexample()
    ensures execution(external_child_model(),|_token:nat| None,external_child_states(),external_child_labels()),
        p::well_formed(external_child_states().last()),s::quiet(external_child_states().last()),
        s::total_active(external_child_states().last()),
        global::support_ranking(external_child_states().last().control,seq![0nat,1nat]),
        !global::support_solution(external_child_states().last().control,global::active(external_child_states().last().control)),
        origin_support_solution(history(external_child_model(),|_token:nat| None,external_child_states(),external_child_labels()),
            external_child_states().last().control,global::active(external_child_states().last().control)),
{
    let states = external_child_states();
    let labels = external_child_labels();
    let model = external_child_model();
    let kind:spec_fn(nat)->Option<usize> = |_token:nat| None;
    p::empty_well_formed::<u64>();
    assert(p::insert_map(states[0],states[1],0));
    p::insert_preservation(states[0],states[1],0);
    assert(s::auxiliary_frame(states[0],states[1],0));
    assert(s::step(model,states[0],states[1],0,c::Rule::Insert));
    assert(s::step(model,states[1],states[2],0,c::Rule::Retire));
    p::retire_preservation(states[1],states[2],0);
    assert(p::insert_map(states[2],states[3],1));
    p::insert_preservation(states[2],states[3],1);
    assert(s::auxiliary_frame(states[2],states[3],1));
    assert(s::step(model,states[2],states[3],1,c::Rule::Insert));
    assert(s::target(states[3],1,ISet::empty()));
    assert(s::step(model,states[3],states[4],1,c::Rule::Begin));
    p::begin_preservation(states[3],states[4],1);
    assert(p::table_map(states[4],states[4],1));
    assert(s::coherent(states[4],1));
    assert(s::step(model,states[4],states[5],1,c::Rule::Finish));
    assert forall|i:int| 0 <= i < labels.len() implies
        s::step(model,states[i],states[i+1],labels[i].0,labels[i].1)
            && admissible(model,kind,states[i],states[i+1],labels[i].0,labels[i].1) by {}
    assert(execution(model,kind,states,labels));
    execution_history(model,kind,states,labels);
    let end = states.last();
    assert forall|n:usize| s::registered(end,n) implies n == 0 || n == 1 by {}
    assert(s::total_active(end));
    assert(s::quiet(end)) by {
        assert forall|n:usize| s::registered(end,n) implies match end.control.fibers[n].phase {
            Phase::Inactive => !(exists|view:ISet<crate::Binding>| s::target(end,n,view)),
            Phase::Active => s::coherent(end,n),
            _ => false,
        } by {}
    }
    assert(global::support_ranking(end.control,seq![0nat,1nat]));
    assert(global::active(end.control).contains(1));
    assert(!global::active(end.control).contains(0));
    assert(!global::support_clause(end.control,global::active(end.control),1));
    execution_quiet_origin_support(model,kind,states,labels);
}

}
