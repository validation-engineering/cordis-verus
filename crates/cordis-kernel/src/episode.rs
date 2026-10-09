//! Executable iterator bookkeeping shared by the host and its proof.
//!
//! A pending stage retains its admission after target drift. Its yielded inverse
//! is appended before the stage can be marked settled, and restoration cannot
//! remove any token while a stage remains open. Tokens name host callbacks;
//! callback execution and the callbacks' inverse laws are separate obligations.
use crate::effects::EffectStack;
use crate::Binding;
use vstd::prelude::*;

verus! {

/// The paper observes complete provider bindings, not their buffer order or
/// multiplicity. Captured vectors themselves remain unchanged across a stage.
pub open spec fn binding_set(bindings: Seq<Binding>) -> ISet<Binding> {
    ISet::new(|b: Binding| bindings.contains(b))
}

fn contains_binding(bindings: &[Binding], binding: Binding) -> (found: bool)
    ensures found == bindings@.contains(binding),
{
    let mut i = 0;
    while i < bindings.len()
        invariant i <= bindings.len(),
            forall|j: int| 0 <= j < i ==> bindings@[j] != binding,
        decreases bindings.len() - i,
    {
        if bindings[i] == binding { return true; }
        i += 1;
    }
    false
}

/// Compare the full (key, realm, provider) identity sets. The normal capture
/// order uses a linear fast path; reordered or repeated entries use a bounded,
/// allocation-free membership fallback. Conflicting identities remain distinct.
pub fn same_bindings(left: &[Binding], right: &[Binding]) -> (same: bool)
    ensures same == (binding_set(left@) == binding_set(right@)),
{
    if left.len() == right.len() {
        let mut i = 0;
        while i < left.len()
            invariant i <= left.len(), left.len() == right.len(),
                forall|j: int| 0 <= j < i ==> left@[j] == right@[j],
            decreases left.len() - i,
        {
            if left[i] != right[i] { break; }
            i += 1;
        }
        if i == left.len() {
            proof { assert(left@ =~= right@); }
            return true;
        }
    }
    let mut i = 0;
    while i < left.len()
        invariant i <= left.len(),
            forall|j: int| 0 <= j < i ==> right@.contains(left@[j]),
        decreases left.len() - i,
    {
        if !contains_binding(right, left[i]) {
            proof {
                assert(binding_set(left@).contains(left@[i as int]));
                assert(!binding_set(right@).contains(left@[i as int]));
            }
            return false;
        }
        i += 1;
    }
    let mut j = 0;
    while j < right.len()
        invariant j <= right.len(),
            forall|k: int| 0 <= k < left.len() ==> right@.contains(left@[k]),
            forall|k: int| 0 <= k < j ==> left@.contains(right@[k]),
        decreases right.len() - j,
    {
        if !contains_binding(left, right[j]) {
            proof {
                assert(binding_set(right@).contains(right@[j as int]));
                assert(!binding_set(left@).contains(right@[j as int]));
            }
            return false;
        }
        j += 1;
    }
    proof { assert(binding_set(left@) =~= binding_set(right@)); }
    true
}

/// This phase belongs to the effect accumulator, not to the independently
/// published kernel control phase. In-flight diversion is delayed until landing.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum AccumulatorPhase { Reloading, Active, Unloading }

pub ghost struct AccumulatorView {
    pub phase: AccumulatorPhase,
    pub committed: Seq<Binding>,
    pub inverses: Seq<usize>,
}

/// Token-level erasure of the paper's effect rules. Context transformations and
/// inverse/continuation witnesses remain separate obligations. These relations
/// describe updates; admission guards are stated on `admit`, and explicit group
/// cancellation is a host extension rather than a proof of target mismatch.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum AccumulatorRule {
    Stutter, Iter(usize), Finish, Divert(Option<usize>), Leave,
}

pub open spec fn accumulator_step(before: AccumulatorView, after: AccumulatorView,
    rule: AccumulatorRule) -> bool
{
    before.committed == after.committed && match rule {
        AccumulatorRule::Stutter => before == after,
        AccumulatorRule::Iter(inverse) => before.phase == AccumulatorPhase::Reloading
            && after.phase == AccumulatorPhase::Reloading
            && after.inverses == before.inverses.push(inverse),
        // The host iterator returns None in a separate poll: its final yielded
        // inverse was already recorded by Iter, so this Finish composes identity.
        AccumulatorRule::Finish => before.phase == AccumulatorPhase::Reloading
            && after.phase == AccumulatorPhase::Active && after.inverses == before.inverses,
        AccumulatorRule::Divert(inverse) => before.phase == AccumulatorPhase::Reloading
            && after.phase == AccumulatorPhase::Unloading
            && after.inverses == match inverse {
                Some(inverse) => before.inverses.push(inverse),
                None => before.inverses,
            },
        AccumulatorRule::Leave => before.phase == AccumulatorPhase::Active
            && after.phase == AccumulatorPhase::Unloading && after.inverses == before.inverses,
    }
}

pub open spec fn boundary_diversion(before: AccumulatorView, after: AccumulatorView) -> bool {
    accumulator_step(before, after, AccumulatorRule::Stutter)
        || accumulator_step(before, after, AccumulatorRule::Divert(None))
        || accumulator_step(before, after, AccumulatorRule::Leave)
}

/// The continuation and inverse accumulator for one independent iterator.
/// Root callback scopes use `scope`; their termination is checked by the host.
pub struct StageProtocol {
    committed: Vec<Binding>,
    inverses: EffectStack,
    in_flight: bool,
    done: bool,
    cancelled: bool,
}

impl StageProtocol {
    pub closed spec fn committed_view(&self) -> Seq<Binding> { self.committed@ }
    pub closed spec fn inverse_view(&self) -> Seq<usize> { self.inverses.view() }
    pub closed spec fn pending(&self) -> bool { self.in_flight }
    pub closed spec fn settled(&self) -> bool { self.done }
    pub closed spec fn cancellation(&self) -> bool { self.cancelled }
    pub closed spec fn wf(&self) -> bool { !(self.in_flight && self.done) }

    /// An admitted pending stage is still abstract Reloading even if concrete
    /// cancellation has arrived. Landing is the linearization point for the
    /// paper's second L-Divert alternative and includes the newly yielded token.
    pub closed spec fn abstract_view(&self) -> AccumulatorView {
        AccumulatorView {
            phase: if !self.done { AccumulatorPhase::Reloading }
                else if self.cancelled { AccumulatorPhase::Unloading }
                else { AccumulatorPhase::Active },
            committed: self.committed@,
            inverses: self.inverses.view(),
        }
    }

    pub fn iterator(committed: Vec<Binding>) -> (out: Self)
        ensures out.wf(), out.committed_view() == committed@,
            out.inverse_view() == Seq::<usize>::empty(),
            !out.pending(), !out.settled(), !out.cancellation(),
    {
        Self { committed, inverses: EffectStack::new(), in_flight: false,
            done: false, cancelled: false }
    }

    /// A non-iterator scope. Root callback completion is outside this protocol.
    pub fn scope() -> (out: Self)
        ensures out.wf(), out.committed_view() == Seq::<Binding>::empty(),
            out.inverse_view() == Seq::<usize>::empty(),
            !out.pending(), out.settled(), !out.cancellation(),
    {
        Self { committed: Vec::new(), inverses: EffectStack::new(), in_flight: false,
            done: true, cancelled: false }
    }

    /// Admit a new stage only against its committed target. Once admitted, a
    /// pending stage may land even after cancellation or loss of the target.
    /// `None` denotes retirement, failure, restart, or an unavailable target.
    /// The exact guard includes sufficiency: a fresh unsettled stage with its
    /// committed target is admitted. This is local enabledness, not a promise
    /// that the host polls it or that its callback terminates (Theorem 73).
    pub fn admit(&mut self, target: Option<&[Binding]>) -> (poll: bool)
        requires old(self).wf(),
        ensures final(self).wf(),
            final(self).committed_view() == old(self).committed_view(),
            final(self).inverse_view() == old(self).inverse_view(),
            poll == final(self).pending(),
            poll == (old(self).pending() || (!old(self).settled()
                && !old(self).cancellation() && target.is_some()
                && binding_set(target.unwrap()@) == binding_set(old(self).committed_view()))),
            final(self).settled() == !poll,
            final(self).cancellation() == (old(self).cancellation()
                || !(target.is_some() && binding_set(target.unwrap()@) == binding_set(old(self).committed_view()))),
            poll ==> accumulator_step(old(self).abstract_view(), final(self).abstract_view(), AccumulatorRule::Stutter),
            !poll ==> boundary_diversion(old(self).abstract_view(), final(self).abstract_view()),
    {
        let matches = match target {
            Some(target) => same_bindings(target, self.committed.as_slice()),
            None => false,
        };
        if !matches { self.cancelled = true; }
        if self.in_flight { return true; }
        if self.done || self.cancelled {
            self.done = true;
            return false;
        }
        self.in_flight = true;
        true
    }

    /// Cancellation preserves an outstanding stage and every inverse. At an
    /// iteration boundary it discards the continuation immediately (L-Divert).
    pub fn cancel(&mut self)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).cancellation(),
            final(self).committed_view() == old(self).committed_view(),
            final(self).inverse_view() == old(self).inverse_view(),
            final(self).pending() == old(self).pending(),
            final(self).settled() == !old(self).pending(),
            boundary_diversion(old(self).abstract_view(), final(self).abstract_view()),
            old(self).pending() ==> accumulator_step(old(self).abstract_view(), final(self).abstract_view(), AccumulatorRule::Stutter),
    {
        self.cancelled = true;
        if !self.in_flight { self.done = true; }
    }

    /// Compose the yielded inverse before accepting another stage or unloading.
    /// A rejected landing is unchanged, so callers can retain their payload.
    pub fn land(&mut self, inverse: usize) -> (accepted: bool)
        requires old(self).wf(),
        ensures final(self).wf(),
            accepted == old(self).pending(),
            final(self).committed_view() == old(self).committed_view(),
            final(self).cancellation() == old(self).cancellation(),
            accepted ==> final(self).inverse_view() == old(self).inverse_view().push(inverse)
                && !final(self).pending()
                && final(self).settled() == old(self).cancellation(),
            !accepted ==> final(self).inverse_view() == old(self).inverse_view()
                && final(self).pending() == old(self).pending()
                && final(self).settled() == old(self).settled(),
            accepted ==> accumulator_step(old(self).abstract_view(), final(self).abstract_view(),
                if old(self).cancellation() { AccumulatorRule::Divert(Some(inverse)) }
                else { AccumulatorRule::Iter(inverse) }),
            !accepted ==> accumulator_step(old(self).abstract_view(), final(self).abstract_view(), AccumulatorRule::Stutter),
    {
        if !self.in_flight { return false; }
        self.inverses.push(inverse);
        self.in_flight = false;
        self.done = self.cancelled;
        true
    }

    /// End-of-iterator or host failure has no newly yielded inverse. A failure's
    /// resource recovery remains the callback author's obligation.
    pub fn end(&mut self) -> (accepted: bool)
        requires old(self).wf(),
        ensures final(self).wf(), accepted == old(self).pending(),
            final(self).committed_view() == old(self).committed_view(),
            final(self).inverse_view() == old(self).inverse_view(),
            final(self).cancellation() == old(self).cancellation(),
            accepted ==> !final(self).pending() && final(self).settled(),
            !accepted ==> final(self).pending() == old(self).pending()
                && final(self).settled() == old(self).settled(),
            accepted ==> accumulator_step(old(self).abstract_view(), final(self).abstract_view(),
                if old(self).cancellation() { AccumulatorRule::Divert(None) }
                else { AccumulatorRule::Finish }),
            !accepted ==> accumulator_step(old(self).abstract_view(), final(self).abstract_view(), AccumulatorRule::Stutter),
    {
        if !self.in_flight { return false; }
        self.in_flight = false;
        self.done = true;
        true
    }

    /// Host callback scopes may register additional cleanup actions. This is an
    /// explicit extension of the paper's one-inverse-per-iteration interface.
    pub fn register(&mut self, inverse: usize)
        requires old(self).wf(),
        ensures final(self).wf(),
            final(self).committed_view() == old(self).committed_view(),
            final(self).inverse_view() == old(self).inverse_view().push(inverse),
            final(self).pending() == old(self).pending(),
            final(self).settled() == old(self).settled(),
            final(self).cancellation() == old(self).cancellation(),
    {
        self.inverses.push(inverse);
    }

    /// Pop precisely the newest inverse after the iterator has settled. The
    /// host additionally enforces the kernel's no-dependent cleanup guard.
    pub fn pop(&mut self) -> (inverse: Option<usize>)
        requires old(self).wf(),
        ensures final(self).wf(),
            final(self).committed_view() == old(self).committed_view(),
            final(self).pending() == old(self).pending(),
            final(self).settled() == old(self).settled(),
            final(self).cancellation() == old(self).cancellation(),
            inverse.is_some() ==> old(self).settled() && !old(self).pending()
                && old(self).inverse_view().len() > 0
                && inverse == Some(old(self).inverse_view().last())
                && final(self).inverse_view() == old(self).inverse_view().drop_last(),
            inverse.is_none() ==> final(self).inverse_view() == old(self).inverse_view(),
            old(self).settled() && old(self).inverse_view().len() > 0 ==> inverse.is_some(),
    {
        if !self.done { return None; }
        self.inverses.pop()
    }

    pub fn is_pending(&self) -> (pending: bool)
        ensures pending == self.pending(),
    { self.in_flight }

    pub fn is_settled(&self) -> (settled: bool)
        ensures settled == self.settled(),
    { self.done }

    pub fn is_empty(&self) -> (empty: bool)
        ensures empty == (self.inverse_view().len() == 0),
    { self.inverses.is_empty() }

    /// This iterator can join L-Finish only with no outstanding stage and with
    /// the same target that admitted its episode. Local group cancellation also
    /// settles the iterator; it does not retire the entire owning fiber. The
    /// kernel separately checks fiber retirement and its current committed view,
    /// and the host separately checks root and other-group completion.
    pub fn can_finish(&self, target: &[Binding]) -> (ready: bool)
        requires self.wf(),
        ensures ready == (self.settled() && !self.pending()
            && binding_set(target@) == binding_set(self.committed_view())),
    {
        self.done && same_bindings(target, self.committed.as_slice())
    }
}

/// A checked executable client of the admission contract. A matching target
/// really enables the first poll; cancellation retains that poll through a
/// missing target until the supplied terminal result lands. This witnesses the
/// Table 1 local admission/late-diversion path, not callback or scheduler
/// termination. The optional token is already supplied by the caller.
pub fn cancelled_admission_witness(committed: Vec<Binding>, target: &[Binding],
    inverse: Option<usize>) -> (out: StageProtocol)
    requires binding_set(target@) == binding_set(committed@),
    ensures out.wf(), out.committed_view() == committed@,
        out.cancellation(), out.settled(), !out.pending(),
        out.inverse_view() == match inverse {
            Some(token) => seq![token],
            None => Seq::<usize>::empty(),
        },
{
    let mut stage = StageProtocol::iterator(committed);
    let _admitted = stage.admit(Some(target));
    assert(_admitted);
    assert(stage.pending() && !stage.settled() && !stage.cancellation());
    stage.cancel();
    let _continued = stage.admit(None);
    assert(_continued && stage.pending() && !stage.settled());
    let _early = stage.pop();
    assert(_early.is_none());
    match inverse {
        Some(token) => { let _accepted = stage.land(token); assert(_accepted); },
        None => { let _accepted = stage.end(); assert(_accepted); },
    }
    let _restarted = stage.admit(Some(target));
    assert(!_restarted);
    stage
}

} // verus!
