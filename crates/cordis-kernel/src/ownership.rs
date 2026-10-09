//! Executable witnesses for Definition 52's child-instantiation primitive.
//!
//! The yielded inverse is the identity of the child actually inserted by this
//! stage. Recovery consumes those identities in reverse order and requests
//! retirement; it never removes a child or waits for the child's lifecycle.
#[cfg(verus_keep_ghost)]
use crate::episode::{accumulator_step, binding_set, AccumulatorRule, AccumulatorView};
use crate::episode::{same_bindings, StageProtocol};
#[cfg(verus_keep_ghost)]
use crate::refinement;
use crate::{Binding, Error, Kernel, Phase, Port};
use vstd::prelude::*;

verus! {

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum ChildError { NotAdmitted, Kernel(Error) }

/// Definition 52 uses the insertion primitive as an effect of its parent. The
/// fresh entry and its exact parent are part of the effect, not an unlabelled
/// external orchestration input.
pub open spec fn child_effect(a: refinement::State, z: refinement::State, actor: usize, child: usize) -> bool {
    refinement::step(a, z, child, refinement::Rule::Insert)
        && z.fibers[child].parent == Some(actor)
}

/// The effect and yielded inverse are one transition of the iterator. The
/// lifecycle phase update is supplied by the enclosing complete calculus rule.
pub open spec fn child_iteration(a: refinement::State, z: refinement::State,
    before: AccumulatorView, after: AccumulatorView, actor: usize, child: usize) -> bool
{
    child_effect(a, z, actor, child)
        && (accumulator_step(before, after, AccumulatorRule::Iter(child))
            || accumulator_step(before, after, AccumulatorRule::Divert(Some(child))))
}

/// A consumed inverse performs O-Retire. It preserves the child's lifecycle,
/// services, and committed dependencies even if the child is still Active.
pub open spec fn child_inverse(a: refinement::State, z: refinement::State, child: usize) -> bool {
    refinement::step(a, z, child, refinement::Rule::Retire)
}

/// L-Unload applies the retirement accumulator before discarding the parent's
/// committed view. It places no requirement on the phases of the children.
pub open spec fn child_unload(a: refinement::State, z: refinement::State, actor: usize, children: Seq<usize>) -> bool {
    exists|middle: refinement::State| retired_children(a, middle, children)
        && refinement::step(middle, z, actor, refinement::Rule::Unload)
}

/// Applying a sequence of child inverses changes only retirement flags. All
/// service tables, lifecycle phases, committed views, and registry entries are
/// preserved; hence an Active child does not prevent parent restoration.
pub open spec fn retired_children(a: refinement::State, z: refinement::State, children: Seq<usize>) -> bool {
    &&& a.fibers.dom() == z.fibers.dom()
    &&& forall|i: int| 0 <= i < children.len() ==> refinement::registered(a, children[i])
    &&& forall|n: usize| refinement::registered(a, n) ==> {
        &&& refinement::interface_same(a.fibers[n], z.fibers[n])
        &&& z.fibers[n].phase == a.fibers[n].phase
        &&& z.fibers[n].committed == a.fibers[n].committed
        &&& z.fibers[n].retired == (a.fibers[n].retired || children.contains(n))
    }
}

pub proof fn retirement_composes(a: refinement::State, middle: refinement::State,
    z: refinement::State, retired: Seq<usize>, child: usize)
    requires retired_children(a, middle, retired), child_inverse(middle, z, child),
    ensures retired_children(a, z, retired.push(child)),
{
    assert(a.fibers.dom() =~= z.fibers.dom()) by {
        assert forall|n: usize| a.fibers.dom().contains(n) == z.fibers.dom().contains(n) by {
            if n != child { assert(refinement::registered(middle, n) == refinement::registered(z, n)); }
        }
    }
    assert forall|i: int| 0 <= i < retired.push(child).len() implies
        refinement::registered(a, retired.push(child)[i]) by {
        if i < retired.len() { assert(retired.push(child)[i] == retired[i]); }
        else { assert(retired.push(child)[i] == child); }
    }
    assert forall|n: usize| refinement::registered(a, n) implies {
        &&& refinement::interface_same(a.fibers[n], z.fibers[n])
        &&& z.fibers[n].phase == a.fibers[n].phase
        &&& z.fibers[n].committed == a.fibers[n].committed
        &&& z.fibers[n].retired == (a.fibers[n].retired || retired.push(child).contains(n))
    } by {
        vstd::seq_lib::lemma_seq_contains_after_push(retired, child, n);
        assert(refinement::registered(middle, n));
        assert(refinement::registered(z, n));
        assert(refinement::interface_same(a.fibers[n], middle.fibers[n]));
        assert(middle.fibers[n].phase == a.fibers[n].phase);
        assert(middle.fibers[n].committed == a.fibers[n].committed);
        assert(middle.fibers[n].retired == (a.fibers[n].retired || retired.contains(n)));
        if n != child { assert(middle.fibers[n] == z.fibers[n]); }
    }
}

/// A concrete child-only effect iterator. Mixed resource/child effects can use
/// the same primitive with the combined calculus's heterogeneous accumulator.
/// Use a handle only with its originating Kernel instance: node identities and
/// episode generations are instance-local. Standalone rollback retires the
/// recorded children without completing the parent's current lifecycle.
pub struct ChildEpisode {
    actor: usize,
    children: Vec<usize>,
    captured: Vec<Binding>,
    generation: Option<u64>,
    protocol: StageProtocol,
}
impl ChildEpisode {
    pub closed spec fn wf(&self) -> bool {
        self.protocol.wf() && self.children@ == self.protocol.inverse_view()
            && self.captured@ == self.protocol.committed_view()
    }
    pub closed spec fn owner(&self) -> usize { self.actor }
    pub closed spec fn captured_generation(&self) -> Option<u64> { self.generation }
    pub closed spec fn generation_extends(&self,prior:&Self) -> bool {
        prior.generation.is_some() ==> self.generation == prior.generation
    }
    pub closed spec fn generation_matches(&self,kernel:&Kernel) -> bool {
        self.generation.is_none() || kernel.generation_of(self.actor) == self.generation
    }

    pub closed spec fn children(&self) -> Seq<usize> { self.children@ }
    pub closed spec fn view(&self) -> AccumulatorView { self.protocol.abstract_view() }
    pub closed spec fn pending(&self) -> bool { self.protocol.pending() }
    pub closed spec fn settled(&self) -> bool { self.protocol.settled() }
    pub closed spec fn cancellation(&self) -> bool { self.protocol.cancellation() }
    pub closed spec fn committed(&self) -> Seq<Binding> { self.protocol.committed_view() }
    /// The checked handle must still describe this Loading activation. Current
    /// target availability is deliberately absent: pending work may still land.
    pub open spec fn current_matches(&self, kernel: &Kernel) -> bool {
        refinement::registered(kernel.paper(), self.owner())
            && kernel.paper().fibers[self.owner()].phase == Phase::Loading
            && self.generation_matches(kernel)
            && binding_set(self.committed()) == kernel.paper().fibers[self.owner()].committed
    }

    pub open spec fn land_enabled(&self, kernel: &Kernel, dependencies: Seq<Port>, provisions: Seq<Port>) -> bool {
        self.pending() && self.current_matches(kernel)
            && kernel.insert_enabled(Some(self.owner()), dependencies, provisions)
    }

    pub closed spec fn retirable(&self, registry: refinement::State) -> bool {
        forall|i: int| 0 <= i < self.children.len() ==> refinement::registered(registry, self.children[i])
    }

    /// Detached low-level accumulator for an already checked binding snapshot.
    /// Its first checked admission/landing captures the live episode generation.
    /// Prefer `attach`, which captures identity immediately. A handle and its
    /// Kernel must belong to the same Kernel instance; IDs are instance-local.
    pub fn new(actor: usize, committed: Vec<Binding>) -> (out: Self)
        ensures out.wf(), out.owner() == actor, out.children() == Seq::<usize>::empty(),
            out.committed() == committed@, !out.pending(), !out.settled(), !out.cancellation(), out.captured_generation().is_none(),
    {
        let mut captured = Vec::new();
        let mut i = 0;
        while i < committed.len()
            invariant i <= committed.len(), captured.len() == i,
                forall|j: int| 0 <= j < i ==> captured[j] == committed[j],
            decreases committed.len() - i,
        {
            captured.push(committed[i]);
            i += 1;
        }
        proof { assert(captured@ =~= committed@); }
        Self { actor, children: Vec::new(), captured, generation:None, protocol: StageProtocol::iterator(committed) }
    }

    /// Read the actor's real committed providers and episode generation.
    /// A later activation with identical bindings cannot reuse this handle.
    /// Subsequent calls must use this same Kernel instance.
    pub fn attach(kernel: &Kernel, actor: usize) -> (result: Result<Self, ChildError>)
        requires kernel.wf(),
        ensures result.is_ok() == (kernel.phase_of(actor) == Some(Phase::Loading)),
            result.is_ok() ==> result.unwrap().wf() && result.unwrap().owner() == actor
            && result.unwrap().children().len() == 0 && !result.unwrap().pending() && !result.unwrap().settled()
            && !result.unwrap().cancellation()
            && result.unwrap().captured_generation().is_some()
            && result.unwrap().captured_generation() == kernel.generation_of(actor)
            && refinement::registered(kernel.paper(), actor) && kernel.paper().fibers[actor].phase == Phase::Loading
            && kernel.paper().fibers[actor].committed == ISet::new(|b: Binding| result.unwrap().committed().contains(b)),
    {
        proof { kernel.paper_observations(actor); }
        if kernel.phase(actor) != Some(Phase::Loading) { return Err(ChildError::Kernel(Error::InvalidState)); }
        let committed = kernel.committed(actor);
        let mut episode = Self::new(actor, committed);
        episode.generation = kernel.episode_generation(actor);
        Ok(episode)
    }

    /// A captured generation rejects a later episode even when its providers
    /// are identical. Detached low-level accumulators bind on first checked use.
    fn check_generation(&self,kernel:&Kernel) -> (result:Result<(),ChildError>)
        ensures result.is_ok() == self.generation_matches(kernel),
    {
        if let Some(expected) = self.generation {
            if kernel.episode_generation(self.actor) != Some(expected) {
                return Err(ChildError::Kernel(Error::Changed));
            }
        }
        Ok(())
    }

    fn check_snapshot(&self, kernel: &Kernel) -> (result: Result<(), ChildError>)
        requires self.wf(), kernel.wf(),
        ensures result.is_ok() == self.current_matches(kernel),
    {
        proof { kernel.paper_observations(self.actor); }
        if kernel.phase(self.actor) != Some(Phase::Loading) { return Err(ChildError::Kernel(Error::InvalidState)); }
        self.check_generation(kernel)?;
        let current = kernel.committed(self.actor);
        if !same_bindings(current.as_slice(), self.captured.as_slice()) {
            return Err(ChildError::Kernel(Error::Changed));
        }
        Ok(())
    }

    /// Inspect the actual landing domain without admitting a stage, capturing
    /// a generation, allocating a child, or consuming an inverse. This check
    /// makes no reservation against intervening registry changes.
    pub fn check_child(&self, kernel: &Kernel, dependencies: &[Port], provisions: &[Port])
        -> (result: Result<(), ChildError>)
        requires self.wf(), kernel.wf(),
        ensures result.is_ok() == self.land_enabled(kernel, dependencies@, provisions@),
    {
        if !self.protocol.is_pending() { return Err(ChildError::NotAdmitted); }
        self.check_snapshot(kernel)?;
        match kernel.check_insert(Some(self.actor), dependencies, provisions) {
            Ok(()) => Ok(()),
            Err(error) => Err(ChildError::Kernel(error)),
        }
    }

    fn check_current(&mut self, kernel: &Kernel) -> (result: Result<(), ChildError>)
        requires old(self).wf(), kernel.wf(),
        ensures final(self).wf(),final(self).owner() == old(self).owner(),
            final(self).children() == old(self).children(),final(self).committed() == old(self).committed(),
            final(self).view() == old(self).view(),final(self).pending() == old(self).pending(),
            final(self).settled() == old(self).settled(),final(self).generation_extends(old(self)),
            final(self).cancellation() == old(self).cancellation(),
            result.is_ok() == (refinement::registered(kernel.paper(), old(self).owner())
                && kernel.paper().fibers[old(self).owner()].phase == Phase::Loading
                && old(self).generation_matches(kernel)
                && binding_set(old(self).committed()) == kernel.paper().fibers[old(self).owner()].committed),
            result.is_err() ==> *final(self) == *old(self),
            result.is_ok() ==> refinement::registered(kernel.paper(), final(self).owner())
                && kernel.paper().fibers[final(self).owner()].phase == Phase::Loading
                && kernel.paper().fibers[final(self).owner()].committed == ISet::new(|b: Binding| final(self).committed().contains(b))
                && final(self).captured_generation().is_some()
                && final(self).captured_generation() == kernel.generation_of(final(self).owner()),
    {
        proof { kernel.paper_observations(self.actor); }
        self.check_snapshot(kernel)?;
        self.generation = kernel.episode_generation(self.actor);
        Ok(())
    }

    /// Checked admission reads both committed and target views from the kernel.
    /// A previously admitted in-flight stage survives retirement/target loss;
    /// a new stage requires the currently published providers to agree.
    pub fn admit_current(&mut self, kernel: &Kernel) -> (result: Result<bool, ChildError>)
        requires old(self).wf(), kernel.wf(),
        ensures !old(self).generation_matches(kernel) ==> result.is_err(), final(self).generation_extends(old(self)), final(self).wf(), final(self).owner() == old(self).owner(),
            final(self).children() == old(self).children(), final(self).committed() == old(self).committed(),
            result.is_ok() == (refinement::registered(kernel.paper(), old(self).owner())
                && kernel.paper().fibers[old(self).owner()].phase == Phase::Loading
                && old(self).generation_matches(kernel)
                && binding_set(old(self).committed()) == kernel.paper().fibers[old(self).owner()].committed),
            result.is_ok() ==> final(self).current_matches(kernel),
            result.is_ok() ==> result.unwrap() == (old(self).pending()
                || (!old(self).settled() && !old(self).cancellation()
                    && refinement::coherent(kernel.paper(), old(self).owner()))),
            result.is_ok() ==> final(self).settled() == !result.unwrap()
                && final(self).cancellation() == (old(self).cancellation()
                    || !refinement::coherent(kernel.paper(), old(self).owner())),
            result.is_ok() ==> final(self).captured_generation().is_some()
                && final(self).captured_generation() == kernel.generation_of(old(self).owner()),
            result.is_ok() ==> result.unwrap() == final(self).pending()
                && refinement::registered(kernel.paper(), old(self).owner())
                && kernel.paper().fibers[old(self).owner()].committed == ISet::new(|b: Binding| old(self).committed().contains(b)),
            result == Ok(true) ==> old(self).pending()
                || refinement::target(kernel.paper(), old(self).owner(), ISet::new(|b: Binding| old(self).committed().contains(b))),
            result.is_ok() && old(self).pending() ==> result == Ok(true),
            result.is_err() ==> final(self).view() == old(self).view()
                && final(self).pending() == old(self).pending() && final(self).settled() == old(self).settled()
                && final(self).cancellation() == old(self).cancellation(),
    {
        self.check_current(kernel)?;
        match kernel.target(self.actor) {
            Some(target) => {
                proof { kernel.paper_captured_target(self.actor, self.committed(), Some(target@)); }
                Ok(self.protocol.admit(Some(target.as_slice())))
            },
            None => {
                proof { kernel.paper_captured_target(self.actor, self.committed(), None); }
                Ok(self.protocol.admit(None))
            },
        }
    }

    /// Low-level protocol admission for explicitly supplied target snapshots.
    /// `admit_current` connects admission to the actual kernel state.
    pub fn admit(&mut self, target: Option<&[Binding]>) -> (accepted: bool)
        requires old(self).wf(),
        ensures final(self).captured_generation() == old(self).captured_generation(), final(self).wf(), final(self).owner() == old(self).owner(),
            final(self).children() == old(self).children(), final(self).committed() == old(self).committed(),
            accepted == final(self).pending(), old(self).pending() ==> accepted,
            accepted == (old(self).pending() || (!old(self).settled() && !old(self).cancellation()
                && target.is_some() && binding_set(target.unwrap()@) == binding_set(old(self).committed()))),
            final(self).settled() == !accepted,
            final(self).cancellation() == (old(self).cancellation()
                || !(target.is_some() && binding_set(target.unwrap()@) == binding_set(old(self).committed()))),
    { self.protocol.admit(target) }

    pub fn cancel(&mut self)
        requires old(self).wf(),
        ensures final(self).captured_generation() == old(self).captured_generation(), final(self).wf(), final(self).owner() == old(self).owner(),
            final(self).children() == old(self).children(), final(self).committed() == old(self).committed(),
            final(self).pending() == old(self).pending(), final(self).settled() == !old(self).pending(),
            final(self).cancellation(),
    { self.protocol.cancel(); }

    /// Execute the admitted instantiation and capture its real retirement
    /// witness before permitting recovery. A retired parent remains registered
    /// and can receive the child yielded by its already-admitted stage.
    pub fn land_child(&mut self, kernel: &mut Kernel, dependencies: Vec<Port>, provisions: Vec<Port>)
        -> (result: Result<usize, ChildError>)
        requires old(self).wf(), old(kernel).wf(),
        ensures result.is_ok() == old(self).land_enabled(old(kernel), dependencies@, provisions@),
            !old(self).generation_matches(old(kernel)) ==> result.is_err(), final(self).generation_extends(old(self)), final(self).wf(), final(kernel).wf(), final(self).owner() == old(self).owner(),
            final(self).committed() == old(self).committed(),
            old(self).retirable(old(kernel).paper()) ==> final(self).retirable(final(kernel).paper()),
            result.is_ok() ==> result.unwrap() == old(kernel).next_id()
                && final(kernel).next_id() == old(kernel).next_id() + 1,
            result.is_err() ==> final(kernel).next_id() == old(kernel).next_id(),
            result.is_ok() ==> final(self).captured_generation().is_some()
                && final(self).captured_generation() == old(kernel).generation_of(old(self).owner())
                && final(self).captured_generation() == final(kernel).generation_of(old(self).owner()),
            result.is_ok() ==> old(self).pending() && !final(self).pending()
                && refinement::registered(old(kernel).paper(), old(self).owner())
                && old(kernel).paper().fibers[old(self).owner()].phase == Phase::Loading
                && old(kernel).paper().fibers[old(self).owner()].committed == ISet::new(|b: Binding| old(self).committed().contains(b))
                && final(self).children() == old(self).children().push(result.unwrap())
                && child_iteration(old(kernel).paper(), final(kernel).paper(), old(self).view(), final(self).view(), old(self).owner(), result.unwrap()),
            result.is_err() ==> final(kernel).unchanged(old(kernel))
                && final(self).children() == old(self).children() && final(self).view() == old(self).view()
                && final(self).pending() == old(self).pending() && final(self).settled() == old(self).settled(),
    {
        if !self.protocol.is_pending() { return Err(ChildError::NotAdmitted); }
        self.check_current(kernel)?;
        match kernel.insert(Some(self.actor), dependencies, provisions) {
            Err(error) => { proof { kernel.unchanged_observations(old(kernel)); } Err(ChildError::Kernel(error)) },
            Ok(child) => {
                proof {
                    kernel.generation_frame(old(kernel),self.actor);
                    assert forall|i: int| old(self).retirable(old(kernel).paper()) && 0 <= i < self.children.len()
                        implies refinement::registered(kernel.paper(), self.children[i]) by {
                        assert(refinement::registered(old(kernel).paper(), self.children[i]));
                        assert(self.children[i] != child);
                    }
                }
                self.children.push(child);
                let _accepted = self.protocol.land(child);
                assert(_accepted);
                Ok(child)
            },
        }
    }

    pub fn end(&mut self) -> (accepted: bool)
        requires old(self).wf(),
        ensures final(self).captured_generation() == old(self).captured_generation(), final(self).wf(), final(self).owner() == old(self).owner(),
            final(self).children() == old(self).children(), final(self).committed() == old(self).committed(),
            accepted == old(self).pending(), accepted ==> final(self).settled() && !final(self).pending(),
    { self.protocol.end() }

    /// The inverse is independent of the child's phase and has no child-join
    /// condition. If an externally removed child is supplied, the rejected
    /// retirement leaves the inverse available to its caller.
    pub fn rollback_one(&mut self, kernel: &mut Kernel) -> (result: Result<Option<usize>, ChildError>)
        requires old(self).wf(), old(kernel).wf(),
        ensures forall|n:usize| final(kernel).is_restoring(n) == old(kernel).is_restoring(n),
            final(kernel).next_id() == old(kernel).next_id(),
            final(self).captured_generation() == old(self).captured_generation(), final(self).wf(), final(kernel).wf(), final(self).owner() == old(self).owner(),
            final(self).committed() == old(self).committed(),
            final(self).pending() == old(self).pending(), final(self).settled() == old(self).settled(),
            old(self).retirable(old(kernel).paper()) ==> final(self).retirable(final(kernel).paper()),
            old(self).retirable(old(kernel).paper()) ==> result.is_ok(),
            (result == Ok(None)) == (!old(self).settled() || old(self).children().len() == 0),
            result.is_ok() && result.unwrap().is_some() ==> old(self).settled()
                && old(self).children().len() > 0
                && result.unwrap().unwrap() == old(self).children().last()
                && final(self).children() == old(self).children().drop_last()
                && child_inverse(old(kernel).paper(), final(kernel).paper(), result.unwrap().unwrap()),
            result.is_err() || result == Ok(None) ==> final(self).children() == old(self).children()
                && final(kernel).unchanged(old(kernel)),
    {
        if !self.protocol.is_settled() || self.children.is_empty() { return Ok(None); }
        let child = self.children[self.children.len() - 1];
        proof { kernel.paper_observations(child); }
        match kernel.retire(child) {
            Err(error) => Err(ChildError::Kernel(error)),
            Ok(()) => {
                let _token = self.protocol.pop();
                assert(_token == Some(child));
                let _popped = self.children.pop();
                assert(_popped == Some(child));
                Ok(Some(child))
            },
        }
    }

    /// Check the entire inverse domain before any retirement occurs. This is
    /// executable because ordinary Rust callers do not enforce ghost premises.
    fn all_registered(&self, kernel: &Kernel) -> (present: bool)
        ensures present == self.retirable(kernel.paper()),
    {
        let mut i = 0;
        while i < self.children.len()
            invariant i <= self.children.len(),
                forall|j: int| 0 <= j < i ==> refinement::registered(kernel.paper(), self.children[j]),
            decreases self.children.len() - i,
        {
            let child = self.children[i];
            proof { kernel.paper_observations(child); }
            if !kernel.contains(child) { return false; }
            i += 1;
        }
        true
    }

    /// Apply the complete accumulator with no predicate on child phases. The
    /// loop preserves each child entry and proves the exact retirement effect;
    /// lifecycle restoration of the parent can immediately follow this call.
    /// Missing child names reject the whole operation without consuming any
    /// inverse, rather than retrying the same failed retirement indefinitely.
    pub fn rollback(&mut self, kernel: &mut Kernel) -> (completed: bool)
        requires old(self).wf(), old(kernel).wf(),
        ensures forall|n:usize| final(kernel).is_restoring(n) == old(kernel).is_restoring(n),
            final(kernel).next_id() == old(kernel).next_id(),
            final(self).captured_generation() == old(self).captured_generation(), final(self).wf(), final(kernel).wf(), final(self).owner() == old(self).owner(),
            final(self).committed() == old(self).committed(),
            final(self).pending() == old(self).pending(), final(self).settled() == old(self).settled(),
            completed == (old(self).settled() && old(self).retirable(old(kernel).paper())),
            completed ==> final(self).children().len() == 0
                && retired_children(old(kernel).paper(), final(kernel).paper(), old(self).children()),
            !completed ==> final(self).children() == old(self).children() && final(kernel).unchanged(old(kernel)),
    {
        if !self.protocol.is_settled() || !self.all_registered(kernel) { return false; }
        let ghost mut retired = Seq::<usize>::empty();
        let ghost initial = old(self).children();
        while !self.children.is_empty()
            invariant self.wf(), kernel.wf(), self.retirable(kernel.paper()), self.settled(),
                self.owner() == old(self).owner(), self.committed() == old(self).committed(),
                self.captured_generation() == old(self).captured_generation(),
                self.pending() == old(self).pending(), self.settled() == old(self).settled(),
                kernel.next_id() == old(kernel).next_id(),
                forall|n:usize| kernel.is_restoring(n) == old(kernel).is_restoring(n),
                retired_children(old(kernel).paper(), kernel.paper(), retired),
                forall|n: usize| initial.contains(n) == (self.children().contains(n) || retired.contains(n)),
            decreases self.children().len(),
        {
            let ghost prior = kernel.paper();
            let ghost children = self.children();
            let _result = self.rollback_one(kernel);
            assert(_result.is_ok() && _result.unwrap().is_some());
            let ghost child = _result.unwrap().unwrap();
            proof {
                retirement_composes(old(kernel).paper(), prior, kernel.paper(), retired, child);
                assert(children == children.drop_last().push(child));
                assert forall|n: usize| initial.contains(n) == (self.children().contains(n) || retired.push(child).contains(n)) by {
                    vstd::seq_lib::lemma_seq_contains_after_push(retired, child, n);
                    vstd::seq_lib::lemma_seq_contains_after_push(children.drop_last(), child, n);
                }
                retired = retired.push(child);
            }
        }
        assert(retired_children(old(kernel).paper(), kernel.paper(), initial)) by {
            assert forall|i: int| 0 <= i < initial.len() implies refinement::registered(old(kernel).paper(), initial[i]) by {
                assert(initial.contains(initial[i]));
                assert(retired.contains(initial[i]));
                let j = choose|j: int| 0 <= j < retired.len() && retired[j] == initial[i];
            }
        }
        true
    }

    /// Execute the complete L-Unload composition: admission checks the actual
    /// kernel dependency guard, the real accumulator retires its children, and
    /// the final kernel step drops the parent's committed view. The accumulator
    /// remains intact when an in-flight stage or consumer blocks admission.
    pub fn finish_restore(&mut self, kernel: &mut Kernel) -> (result: Result<(), ChildError>)
        requires old(self).wf(), old(kernel).wf(),
        ensures final(kernel).next_id() == old(kernel).next_id(),
            final(self).captured_generation() == old(self).captured_generation(), final(self).wf(), final(kernel).wf(), final(self).owner() == old(self).owner(),
            final(self).committed() == old(self).committed(),
            !old(self).retirable(old(kernel).paper()) ==> result.is_err()
                && final(self).children() == old(self).children() && final(kernel).unchanged(old(kernel)),
            result.is_err() ==> final(kernel).unchanged(old(kernel)) && final(self).children() == old(self).children(),
            final(self).pending() == old(self).pending(), final(self).settled() == old(self).settled(),
            result.is_ok() ==> old(self).generation_matches(old(kernel)),
            !old(self).generation_matches(old(kernel)) ==> result.is_err()
                && final(kernel).unchanged(old(kernel)) && final(self).children() == old(self).children(),
            result.is_ok() ==> final(self).children().len() == 0
                && child_unload(old(kernel).paper(), final(kernel).paper(), old(self).owner(), old(self).children()),
    {
        if !self.protocol.is_settled() { return Err(ChildError::NotAdmitted); }
        self.check_generation(kernel)?;
        if !self.all_registered(kernel) { return Err(ChildError::Kernel(Error::Unknown)); }
        match kernel.begin_cleanup(self.actor) {
            Err(error) => Err(ChildError::Kernel(error)),
            Ok(()) => {
                let _completed = self.rollback(kernel);
                assert(_completed);
                let ghost middle = kernel.paper();
                match kernel.finish_cleanup(self.actor) {
                    Err(error) => Err(ChildError::Kernel(error)),
                    Ok(()) => {
                        assert(retired_children(old(kernel).paper(), middle, old(self).children()));
                        assert(child_unload(old(kernel).paper(), kernel.paper(), self.actor, old(self).children()));
                        Ok(())
                    },
                }
            },
        }
    }

    pub fn child_at(&self, index: usize) -> (child: Option<usize>)
        ensures child == if index < self.children().len() { Some(self.children()[index as int]) } else { None },
    {
        if index < self.children.len() { Some(self.children[index]) } else { None }
    }

    pub fn is_settled(&self) -> (settled: bool)
        ensures settled == self.settled(),
    { self.protocol.is_settled() }

    pub fn is_pending(&self) -> (pending: bool)
        ensures pending == self.pending(),
    { self.protocol.is_pending() }

    pub fn len(&self) -> (len: usize)
        ensures len == self.children().len(),
    { self.children.len() }

    pub fn is_empty(&self) -> (empty: bool)
        ensures empty == (self.children().len() == 0),
    { self.children.is_empty() }
}
} // verus!
