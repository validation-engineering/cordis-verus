//! Executable lifecycle safety kernel. All state-changing methods are verified.
//! Host callbacks are deliberately outside this crate's proof boundary.
use vstd::prelude::*;
pub mod action_ledger;
pub mod administrative_orchestration;
pub mod alpha;
pub mod calculus;
pub mod canonical;
pub mod causal_normalization;
pub mod child_driver;
pub mod child_history;
pub mod cleanup_journal;
pub mod cleanup_queue;
pub mod coeffects;
pub mod contexts;
pub mod deletion;
pub mod dependent_grammar;
pub mod dependent_lift;
pub mod driver;
pub mod effects;
pub mod entangled;
pub mod episode;
pub mod foundations;
pub mod fresh_recovery;
pub mod global;
pub mod grammar_lift;
pub mod grammar_ordering;
pub mod grammar_recovery;
pub mod history;
pub mod indexed_ordering;
pub mod iterator_bridge;
pub mod iterator_independence;
pub mod iterators;
pub mod lifecycle_actions;
pub mod lifecycle_ordering;
pub mod lifecycle_state;
pub mod mediated;
pub mod mixed_driver;
pub mod mixed_examples;
pub mod mixed_grammar;
pub mod mixed_orchestration;
pub mod mixed_ordering;
pub mod mixed_recovery;
pub mod mixed_syntax;
pub mod mixed_transport;
pub mod mixed_transposition;
pub mod monoid;
pub mod observation;
pub mod observational_algebra;
pub mod observational_examples;
pub mod observational_execution;
pub mod observational_grammar;
pub mod observational_lift;
pub mod observational_recovery;
pub mod operation_history;
pub mod ownership;
pub mod paper_counterexamples;
pub mod partial_domains;
pub mod partial_independence;
pub mod permutation;
pub mod preservation;
pub mod program;
pub mod program_normal_form;
pub mod program_refinement;
pub mod program_trace;
pub mod progress;
pub mod projection;
pub mod provision_coverage;
pub mod provision_history;
pub mod publication;
pub mod quotient;
pub mod recovery_examples;
pub mod recursive_context;
pub mod refinement;
pub mod resources;
pub mod rule_frames;
pub mod semantics;
pub mod terminal_episode;
pub mod termination;
pub mod witnessed;
pub mod xor_recovery_algebra;

verus! {

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum Phase { Inactive, Loading, Active, Unloading }
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum Error { Unknown, InvalidState, Retired, MissingDependency, Conflict, Changed, Relied, Children, Capacity }
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub struct Port { pub key: u64, pub realm: u64 }
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub struct Binding { pub key: u64, pub realm: u64, pub provider: usize }
#[derive(Copy, Clone)]
struct Node { present: bool, retired: bool, phase: Phase, restoring: bool, parent: Option<usize>, generation:u64 }
#[derive(Copy, Clone)]
struct Declaration { owner: usize, port: Port, provides: bool }
#[derive(Copy, Clone)]
struct Link { consumer: usize, binding: Binding, live: bool }

/// Duplicate declaration entries are rejected by the executable API even
/// though the paper represents an interface as a set.
pub open spec fn distinct_ports(ports: Seq<Port>) -> bool {
    forall|i: int, j: int| 0 <= i < j < ports.len() ==> ports[i] != ports[j]
}

pub struct Kernel { nodes: Vec<Node>, declarations: Vec<Declaration>, links: Vec<Link> }

impl Default for Kernel {
    fn default() -> Self { Self::new() }
}

impl Kernel {
    /// Projection into the paper's control-state semantics. The restoration
    /// admission flag and tombstone/declaration storage are implementation detail.
    /// Public observation bridge for modular refinements of the private buffers.
    pub proof fn paper_observations(&self, id: usize)
        ensures self.registered(id) == refinement::registered(self.paper(), id),
            self.generation_of(id).is_some() == self.registered(id),
            self.registered(id) ==> id < self.next_id(),
            self.phase_of(id) == if refinement::registered(self.paper(), id) {
                Some(self.paper().fibers[id].phase)
            } else { None },
            self.is_retired(id) == (refinement::registered(self.paper(), id) && self.paper().fibers[id].retired),
            self.registered(id) ==> (forall|b: Binding| self.binding_recorded(id, b) == self.paper().fibers[id].committed.contains(b)),
    { }
    pub closed spec fn paper(&self) -> refinement::State {
        refinement::State { fibers: IMap::new(|id: usize| self.registered(id), |id: usize| self.paper_fiber(id)) }
    }
    spec fn paper_fiber(&self, id: usize) -> refinement::Fiber {
        refinement::Fiber {
            parent: self.nodes[id as int].parent,
            retired: self.nodes[id as int].retired,
            phase: self.nodes[id as int].phase,
            dependencies: ISet::new(|p: Port| Self::declares(self.declarations@, id, p, false)),
            provisions: ISet::new(|p: Port| Self::declares(self.declarations@, id, p, true)),
            committed: ISet::new(|b: Binding| self.binding_recorded(id, b)),
        }
    }
    /// Episode generation is implementation metadata, absent from the paper
    /// projection. It changes only when a new Loading episode begins.
    pub closed spec fn generation_of(&self,id:usize) -> Option<u64> {
        if self.registered(id) {Some(self.nodes[id as int].generation)} else {None}
    }
    pub closed spec fn generations_preserved(&self,prior:&Self) -> bool {
        self.nodes.len() >= prior.nodes.len() && forall|i:int| 0 <= i < prior.nodes.len()
            ==> self.nodes[i].generation == prior.nodes[i].generation
    }
    pub proof fn generation_frame(&self,prior:&Self,id:usize)
        requires self.generations_preserved(prior),self.registered(id),prior.registered(id),
        ensures self.generation_of(id) == prior.generation_of(id),
    { }
    pub fn episode_generation(&self,id:usize) -> (generation:Option<u64>)
        ensures generation == self.generation_of(id),
    {
        if self.contains(id) {Some(self.nodes[id].generation)} else {None}
    }
    pub closed spec fn unchanged(&self, prior: &Self) -> bool {
        self.nodes@ == prior.nodes@ && self.declarations@ == prior.declarations@ && self.links@ == prior.links@
    }
    pub proof fn unchanged_observations(&self, prior: &Self)
        requires self.unchanged(prior),
        ensures self.paper() == prior.paper(), self.next_id() == prior.next_id(),
            self.generations_preserved(prior),
    {
        assert forall|n: usize, b: Binding| self.binding_recorded(n, b) == prior.binding_recorded(n, b) by { }
        self.paper_stutter(prior);
    }
    spec fn nodes_frame(&self, prior: &Self, id: usize) -> bool {
        forall|n: usize| n != id ==> self.registered(n) == prior.registered(n)
            && (self.registered(n) ==> self.nodes[n as int] == prior.nodes[n as int])
    }
    spec fn declarations_frame(&self, prior: &Self, id: usize) -> bool {
        forall|n: usize, p: Port, provides: bool| n != id && self.registered(n)
            ==> Self::declares(self.declarations@, n, p, provides) == Self::declares(prior.declarations@, n, p, provides)
    }
    pub closed spec fn commitments_frame(&self, prior: &Self, id: usize) -> bool {
        forall|n: usize, b: Binding| n != id ==> self.binding_recorded(n, b) == prior.binding_recorded(n, b)
    }
    proof fn paper_frame(&self, prior: &Self, id: usize)
        requires self.nodes_frame(prior, id), self.declarations_frame(prior, id), self.commitments_frame(prior, id),
        ensures refinement::frame(prior.paper(), self.paper(), id),
    {
        assert forall|n: usize| n != id implies refinement::registered(prior.paper(), n) == refinement::registered(self.paper(), n)
            && (refinement::registered(prior.paper(), n) ==> prior.paper().fibers[n] == self.paper().fibers[n]) by {
            if self.registered(n) {
                assert(self.paper_fiber(n).dependencies =~= prior.paper_fiber(n).dependencies);
                assert(self.paper_fiber(n).provisions =~= prior.paper_fiber(n).provisions);
                assert(self.paper_fiber(n).committed =~= prior.paper_fiber(n).committed);
            }
        }
    }
    proof fn paper_stutter(&self, prior: &Self)
        requires self.nodes@ == prior.nodes@, self.same_interfaces(prior), self.same_live_bindings(prior),
        ensures self.paper() == prior.paper(),
    {
        assert(self.paper().fibers =~= prior.paper().fibers) by {
            assert forall|n: usize| self.registered(n) implies self.paper().fibers[n] == prior.paper().fibers[n] by {
                assert(self.paper_fiber(n).dependencies =~= prior.paper_fiber(n).dependencies);
                assert(self.paper_fiber(n).provisions =~= prior.paper_fiber(n).provisions);
                assert(self.paper_fiber(n).committed =~= prior.paper_fiber(n).committed);
            }
        }
    }
    proof fn paper_target(&self, source: &Self, id: usize)
        requires self.committed_from(source, id),
        ensures refinement::target(source.paper(), id, self.paper_fiber(id).committed),
    {
        assert forall|b: Binding| self.paper_fiber(id).committed.contains(b)
            implies source.paper_fiber(id).dependencies.contains(Port { key: b.key, realm: b.realm })
                && refinement::publishes(source.paper(), Port { key: b.key, realm: b.realm }, b.provider) by {
            let j = choose|j: int| 0 <= j < self.links.len() && self.links[j].live && self.links[j].consumer == id && self.links[j].binding == b;
            assert(source.binding_is_target(id, self.links[j].binding));
        }
        assert forall|p: Port| source.paper_fiber(id).dependencies.contains(p)
            implies exists|b: Binding| self.paper_fiber(id).committed.contains(b) && b.key == p.key && b.realm == p.realm by {
            let j = choose|j: int| 0 <= j < source.declarations.len() && !source.declarations[j].provides && source.declarations[j].owner == id && source.declarations[j].port == p;
            let k = choose|k: int| 0 <= k < self.links.len() && self.links[k].live && self.links[k].consumer == id
                && self.links[k].binding.key == p.key && self.links[k].binding.realm == p.realm;
            assert(self.paper_fiber(id).committed.contains(self.links[k].binding));
        }
    }
    pub proof fn paper_target_vector(&self, id: usize, bindings: Seq<Binding>)
        requires self.complete_target(id, bindings),
        ensures refinement::target(self.paper(), id, ISet::new(|b: Binding| bindings.contains(b))),
    {
        let view = ISet::new(|b: Binding| bindings.contains(b));
        assert forall|b: Binding| view.contains(b)
            implies self.paper_fiber(id).dependencies.contains(Port { key: b.key, realm: b.realm })
                && refinement::publishes(self.paper(), Port { key: b.key, realm: b.realm }, b.provider) by {
            let j = choose|j: int| 0 <= j < bindings.len() && bindings[j] == b;
            assert(self.binding_is_target(id, bindings[j]));
        }
        assert forall|p: Port| self.paper_fiber(id).dependencies.contains(p)
            implies exists|b: Binding| view.contains(b) && b.key == p.key && b.realm == p.realm by {
            let j = choose|j: int| 0 <= j < self.declarations.len() && !self.declarations[j].provides && self.declarations[j].owner == id && self.declarations[j].port == p;
            let k = choose|k: int| 0 <= k < bindings.len() && bindings[k].key == p.key && bindings[k].realm == p.realm;
            assert(view.contains(bindings[k]));
        }
    }
    proof fn paper_phase_change(&self, prior: &Self, id: usize, phase: Phase)
        requires self.registered(id), prior.registered(id), self.nodes_frame(prior, id),
            self.declarations@ == prior.declarations@, self.links@ == prior.links@,
            self.nodes[id as int].parent == prior.nodes[id as int].parent,
            self.nodes[id as int].retired == prior.nodes[id as int].retired,
            self.nodes[id as int].phase == phase,
        ensures refinement::phase_change(prior.paper(), self.paper(), id, phase),
    {
        self.paper_frame(prior, id);
        assert(self.paper_fiber(id).dependencies =~= prior.paper_fiber(id).dependencies);
        assert(self.paper_fiber(id).provisions =~= prior.paper_fiber(id).provisions);
        assert(self.paper_fiber(id).committed =~= prior.paper_fiber(id).committed);
    }

    proof fn links_preserve_other_commitments(&self, prior: &Self, id: usize)
        requires self.links.len() == prior.links.len(),
            forall|j: int| 0 <= j < self.links.len() ==> self.links[j].consumer == prior.links[j].consumer
                && (self.links[j].consumer != id ==> self.links[j] == prior.links[j]),
        ensures self.commitments_frame(prior, id),
    {
        assert forall|n: usize, b: Binding| n != id implies self.binding_recorded(n, b) == prior.binding_recorded(n, b) by {
            if self.binding_recorded(n, b) {
                let j = choose|j: int| 0 <= j < self.links.len() && self.links[j].live && self.links[j].consumer == n && self.links[j].binding == b;
                assert(prior.links[j] == self.links[j]);
            }
            if prior.binding_recorded(n, b) {
                let j = choose|j: int| 0 <= j < prior.links.len() && prior.links[j].live && prior.links[j].consumer == n && prior.links[j].binding == b;
                assert(prior.links[j] == self.links[j]);
            }
        }
    }
    /// Every concrete invariant state projects to a well-formed paper registry
    /// with functional committed provider views. This theorem is independent of
    /// the operation that produced the state.
    pub proof fn refines_paper(&self)
        requires self.wf(),
        ensures refinement::well_formed(self.paper()),
    {
        let s = self.paper();
        assert forall|n: usize| refinement::registered(s, n) implies n < self.nodes.len() by { }
        assert(refinement::name_bound(s, self.nodes.len() as nat));
        assert(exists|bound: nat| refinement::name_bound(s, bound));
        assert forall|n: usize| refinement::registered(s, n) implies match s.fibers[n].parent {
            Some(p) => refinement::registered(s, p) && p < n,
            None => true,
        } by { assert(Self::node_ok(self.nodes@, n as int)); }
        let rank = |n: usize| n as nat;
        assert(refinement::parent_ranking(s, rank));
        assert(exists|rank: spec_fn(usize) -> nat| refinement::parent_ranking(s, rank));
        assert forall|n: usize, m: usize, p: Port| refinement::registered(s, n) && refinement::registered(s, m)
            && s.fibers[n].provisions.contains(p) && s.fibers[m].provisions.contains(p) implies n == m by {
            let a = choose|a: int| 0 <= a < self.declarations.len() && self.declarations[a].owner == n && self.declarations[a].port == p && self.declarations[a].provides;
            let b = choose|b: int| 0 <= b < self.declarations.len() && self.declarations[b].owner == m && self.declarations[b].port == p && self.declarations[b].provides;
            assert(self.declarations[a].owner == self.declarations[b].owner);
        }
        assert forall|n: usize, b: Binding| refinement::registered(s, n) && s.fibers[n].committed.contains(b) implies {
            &&& s.fibers[n].phase != Phase::Inactive
            &&& s.fibers[n].dependencies.contains(Port { key: b.key, realm: b.realm })
            &&& refinement::registered(s, b.provider) && s.fibers[b.provider].phase != Phase::Inactive
            &&& s.fibers[b.provider].provisions.contains(Port { key: b.key, realm: b.realm })
            &&& b.provider != n
        } by {
            let j = choose|j: int| 0 <= j < self.links.len() && self.links[j].live && self.links[j].consumer == n && self.links[j].binding == b;
            assert(Self::link_ok(self.nodes@, self.links[j]));
            assert(Self::typed_link(self.declarations@, self.links[j]));
            if b.provider == n { assert(j < j); }
        }
        assert forall|n: usize, p: Port| refinement::registered(s, n) && s.fibers[n].phase != Phase::Inactive && s.fibers[n].dependencies.contains(p)
            implies exists|b: Binding| s.fibers[n].committed.contains(b) && b.key == p.key && b.realm == p.realm by {
            let d = choose|d: int| 0 <= d < self.declarations.len() && self.declarations[d].owner == n && self.declarations[d].port == p && !self.declarations[d].provides;
            let j = choose|j: int| 0 <= j < self.links.len() && self.links[j].live && self.links[j].consumer == n
                && self.links[j].binding.key == p.key && self.links[j].binding.realm == p.realm;
            assert(s.fibers[n].committed.contains(self.links[j].binding));
        }
        assert forall|n: usize, a: Binding, b: Binding| refinement::registered(s, n)
            && s.fibers[n].committed.contains(a) && s.fibers[n].committed.contains(b)
            && a.key == b.key && a.realm == b.realm implies a.provider == b.provider by {
            let p = Port { key: a.key, realm: a.realm };
            assert(s.fibers[a.provider].provisions.contains(p));
            assert(s.fibers[b.provider].provisions.contains(p));
        }
    }
    pub closed spec fn registered(&self, id: usize) -> bool {
        id < self.nodes.len() && self.nodes[id as int].present
    }
    pub closed spec fn next_id(&self) -> nat { self.nodes.len() as nat }
    pub closed spec fn phase_of(&self, id: usize) -> Option<Phase> {
        if self.registered(id) { Some(self.nodes[id as int].phase) } else { None }
    }
    pub closed spec fn is_retired(&self, id: usize) -> bool {
        self.registered(id) && self.nodes[id as int].retired
    }
    pub closed spec fn is_restoring(&self, id: usize) -> bool {
        self.registered(id) && self.nodes[id as int].restoring
    }
    pub closed spec fn no_committed(&self, id: usize) -> bool {
        forall|i: int| 0 <= i < self.links.len() ==> !(self.links[i].live && self.links[i].consumer == id)
    }
    pub closed spec fn active_provider(&self, id: usize) -> bool {
        id < self.nodes.len() && self.nodes[id as int].present
            && self.nodes[id as int].phase == Phase::Active && !self.nodes[id as int].restoring
    }
    pub closed spec fn resolves_to(&self, port: Port, provider: usize) -> bool {
        self.active_provider(provider) && exists|i: int| 0 <= i < self.declarations.len()
            && self.declarations[i].provides && self.declarations[i].owner == provider
            && self.declarations[i].port == port
    }
    pub closed spec fn has_provider(&self, port: Port) -> bool {
        exists|i: int| 0 <= i < self.declarations.len() && self.declarations[i].provides
            && self.declarations[i].port == port && self.active_provider(self.declarations[i].owner)
    }
    pub closed spec fn binding_is_target(&self, id: usize, binding: Binding) -> bool {
        &&& self.resolves_to(Port { key: binding.key, realm: binding.realm }, binding.provider)
        &&& exists|i: int| 0 <= i < self.declarations.len() && !self.declarations[i].provides
            && self.declarations[i].owner == id
            && self.declarations[i].port == (Port { key: binding.key, realm: binding.realm })
    }
    pub closed spec fn view_has_port(bindings: Seq<Binding>, port: Port) -> bool {
        exists|j: int| 0 <= j < bindings.len() && bindings[j].key == port.key && bindings[j].realm == port.realm
    }
    pub closed spec fn complete_target(&self, id: usize, bindings: Seq<Binding>) -> bool {
        &&& self.registered(id) && !self.nodes[id as int].retired
        &&& forall|i: int| 0 <= i < bindings.len() ==> self.binding_is_target(id, bindings[i])
        &&& forall|i: int| 0 <= i < self.declarations.len() && !self.declarations[i].provides && self.declarations[i].owner == id
            ==> Self::view_has_port(bindings, self.declarations[i].port)
    }
    /// Executable L-Begin admission includes the bounded episode-generation
    /// counter, which is erased by the paper control projection.
    pub closed spec fn begin_enabled(&self, id: usize) -> bool {
        &&& self.phase_of(id) == Some(Phase::Inactive)
        &&& !self.unavailable(id)
        &&& self.generation_of(id).is_some()
        &&& self.generation_of(id).unwrap() < u64::MAX
    }
    pub closed spec fn unavailable(&self, id: usize) -> bool {
        !self.registered(id) || self.nodes[id as int].retired
            || exists|i: int| 0 <= i < self.declarations.len() && !self.declarations[i].provides
                && self.declarations[i].owner == id && !self.has_provider(self.declarations[i].port)
    }
    pub closed spec fn binding_recorded(&self, id: usize, binding: Binding) -> bool {
        exists|k: int| 0 <= k < self.links.len() && self.links[k].live
            && self.links[k].consumer == id && self.links[k].binding == binding
    }
    pub closed spec fn all_bindings_in(&self, id: usize, out: Seq<Binding>) -> bool {
        forall|j: int| 0 <= j < self.links.len() && self.links[j].live && self.links[j].consumer == id
            ==> out.contains(self.links[j].binding)
    }
    pub closed spec fn committed_from(&self, source: &Self, id: usize) -> bool {
        &&& source.registered(id) && !source.nodes[id as int].retired
        &&& forall|i: int| 0 <= i < self.links.len() && self.links[i].live && self.links[i].consumer == id
            ==> source.binding_is_target(id, self.links[i].binding)
        &&& forall|i: int| 0 <= i < source.declarations.len() && !source.declarations[i].provides && source.declarations[i].owner == id
            ==> exists|j: int| 0 <= j < self.links.len() && self.links[j].live && self.links[j].consumer == id
                && self.links[j].binding.key == source.declarations[i].port.key && self.links[j].binding.realm == source.declarations[i].port.realm
    }
    pub closed spec fn coherent(&self, id: usize) -> bool { self.committed_from(self, id) }
    /// The concrete membership contract and the paper target relation agree.
    /// Ordering and multiplicity of the private buffers are not paper guards.
    #[verifier::spinoff_prover]
    pub proof fn paper_coherence(&self, id: usize)
        requires self.wf(),
        ensures self.coherent(id) == refinement::coherent(self.paper(), id),
    {
        if self.coherent(id) { self.paper_target(self, id); }
        if refinement::coherent(self.paper(), id) {
            assert forall|j: int| 0 <= j < self.links.len() && self.links[j].live && self.links[j].consumer == id
                implies self.binding_is_target(id, self.links[j].binding) by {
                let b = self.links[j].binding;
                let p = Port { key: b.key, realm: b.realm };
                assert(self.paper_fiber(id).committed.contains(b));
                assert(refinement::publishes(self.paper(), p, b.provider));
                assert(Self::node_ok(self.nodes@, b.provider as int));
                assert(self.active_provider(b.provider));
                assert(Self::declares(self.declarations@, b.provider, p, true));
                assert(self.resolves_to(p, b.provider));
                assert(Self::declares(self.declarations@, id, p, false));
            }
            assert forall|i: int| 0 <= i < self.declarations.len() && !self.declarations[i].provides
                && self.declarations[i].owner == id
                implies exists|j: int| 0 <= j < self.links.len() && self.links[j].live && self.links[j].consumer == id
                    && self.links[j].binding.key == self.declarations[i].port.key
                    && self.links[j].binding.realm == self.declarations[i].port.realm by {
                let p = self.declarations[i].port;
                assert(self.paper_fiber(id).dependencies.contains(p));
                let b = choose|b: Binding| self.paper_fiber(id).committed.contains(b) && b.key == p.key && b.realm == p.realm;
                assert(self.binding_recorded(id, b));
            }
        }
    }
    /// Connect a real target observation to an episode captured by L-Begin.
    /// The invariant records binding identities as a set, so admission must not
    /// add a private-vector ordering or multiplicity premise.
    pub proof fn paper_captured_target(&self, id: usize, captured: Seq<Binding>, target: Option<Seq<Binding>>)
        requires self.wf(), refinement::registered(self.paper(), id),
            self.paper().fibers[id].phase == Phase::Loading,
            episode::binding_set(captured) == self.paper().fibers[id].committed,
            target.is_some() ==> self.complete_target(id, target.unwrap()),
            target.is_none() ==> self.unavailable(id),
        ensures (target.is_some() && episode::binding_set(target.unwrap()) == episode::binding_set(captured))
            == refinement::coherent(self.paper(), id),
    {
        self.paper_coherence(id);
        if let Some(bindings) = target {
            self.refines_paper();
            self.paper_target_vector(id, bindings);
            refinement::available_installed_coherent(self.paper(), id, episode::binding_set(bindings));
            refinement::target_unique(self.paper(), id, episode::binding_set(bindings), episode::binding_set(captured));
        } else {
            self.unavailable_not_coherent(id);
        }
    }
    pub closed spec fn iteration_enabled(&self, id: usize) -> bool {
        self.phase_of(id) == Some(Phase::Loading) && self.coherent(id)
    }
    /// The actual admission predicate is exactly Table 1's control guard.
    pub proof fn paper_iteration_guard(&self, id: usize)
        requires self.wf(),
        ensures self.iteration_enabled(id) == (refinement::registered(self.paper(), id)
            && self.paper().fibers[id].phase == Phase::Loading && refinement::coherent(self.paper(), id)),
    {
        self.paper_coherence(id);
        self.paper_observations(id);
    }
    pub closed spec fn same_bindings(&self, other: &Self) -> bool { self.links@ == other.links@ }
    pub closed spec fn restoration_guarded(&self, id: usize) -> bool {
        id < self.nodes.len() && self.nodes[id as int].restoring
            && forall|j: int| 0 <= j < self.links.len() ==> !(self.links[j].live && self.links[j].binding.provider == id)
    }

    /// Registered providers cannot collide, including inactive/retired fibers.
    pub closed spec fn exclusive_provisions(&self) -> bool {
        Self::unique_provisions(self.nodes@, self.declarations@)
    }
    spec fn unique_provisions(nodes: Seq<Node>, declarations: Seq<Declaration>) -> bool {
        forall|i: int, j: int| 0 <= i < declarations.len() && 0 <= j < declarations.len()
            && declarations[i].provides && declarations[j].provides
            && nodes[declarations[i].owner as int].present
            && nodes[declarations[j].owner as int].present
            && declarations[i].port == declarations[j].port
            ==> declarations[i].owner == declarations[j].owner
    }
    spec fn provision_admissible(nodes: Seq<Node>, declarations: Seq<Declaration>, port: Port) -> bool {
        forall|i: int| 0 <= i < declarations.len() && declarations[i].provides && nodes[declarations[i].owner as int].present
            ==> declarations[i].port != port
    }
    pub closed spec fn provisions_available(&self, ports: Seq<Port>) -> bool {
        distinct_ports(ports) && forall|i: int| 0 <= i < ports.len()
            ==> Self::provision_admissible(self.nodes@, self.declarations@, ports[i])
    }
    /// The concrete insertion domain includes bounded identities and distinct
    /// declarations. Neither dependency availability nor parent activity is
    /// required; a retired but registered owner still reserves its provisions.
    pub closed spec fn insert_enabled(&self, parent: Option<usize>, dependencies: Seq<Port>, provisions: Seq<Port>) -> bool {
        &&& self.nodes.len() < usize::MAX
        &&& (parent.is_some() ==> self.registered(parent.unwrap()))
        &&& self.provisions_available(provisions)
        &&& distinct_ports(dependencies)
    }

    /// The runtime insertion guard is the paper's parent/reservation guard,
    /// together with bounded IDs and duplicate-free input declarations.
    #[verifier::spinoff_prover]
    pub proof fn paper_insert_domain(&self, parent: Option<usize>, dependencies: Seq<Port>, provisions: Seq<Port>)
        requires self.wf(),
        ensures self.insert_enabled(parent, dependencies, provisions)
            == (self.next_id() < usize::MAX && distinct_ports(dependencies) && distinct_ports(provisions)
                && refinement::insertion_domain(self.paper(), parent, ISet::new(|p: Port| provisions.contains(p)))),
    {
        if let Some(p) = parent { self.paper_observations(p); }
        let reserved = ISet::new(|p: Port| provisions.contains(p));
        if self.provisions_available(provisions) {
            assert forall|n: usize, p: Port| refinement::registered(self.paper(), n)
                && self.paper().fibers[n].provisions.contains(p) implies !reserved.contains(p) by {
                let j = choose|j: int| 0 <= j < self.declarations.len() && self.declarations[j].owner == n
                    && self.declarations[j].provides && self.declarations[j].port == p;
                if reserved.contains(p) {
                    let i = choose|i: int| 0 <= i < provisions.len() && provisions[i] == p;
                    assert(Self::provision_admissible(self.nodes@, self.declarations@, provisions[i]));
                }
            }
        }
        if refinement::insertion_domain(self.paper(), parent, reserved) {
            assert forall|i: int| 0 <= i < provisions.len() implies
                Self::provision_admissible(self.nodes@, self.declarations@, provisions[i]) by {
                assert(reserved.contains(provisions[i]));
                assert forall|j: int| 0 <= j < self.declarations.len() && self.declarations[j].provides
                    && self.nodes[self.declarations[j].owner as int].present implies self.declarations[j].port != provisions[i] by {
                    let d = self.declarations[j];
                    assert(refinement::registered(self.paper(), d.owner));
                    assert(self.paper().fibers[d.owner].provisions.contains(d.port));
                }
            }
        }
    }
    fn check_provisions(&self, ports: &[Port]) -> (ok: bool)
        requires self.wf(),
        ensures ok == self.provisions_available(ports@),
            ok ==> (forall|i: int| 0 <= i < ports.len() ==> Self::provision_admissible(self.nodes@, self.declarations@, ports[i]))
            && (forall|i: int, j: int| 0 <= i < j < ports.len() ==> ports[i] != ports[j]),
    {
        let mut i = 0;
        while i < ports.len()
            invariant i <= ports.len(), self.wf(),
                forall|a: int| 0 <= a < i ==> Self::provision_admissible(self.nodes@, self.declarations@, ports[a]),
                forall|a: int, b: int| 0 <= a < b < i ==> ports[a] != ports[b],
            decreases ports.len() - i,
        {
            let p = ports[i];
            let mut j = 0;
            while j < i
                invariant j <= i, i < ports.len(), p == ports@[i as int],
                    forall|a: int| 0 <= a < j ==> ports[a] != p,
                decreases i - j,
            {
                if ports[j] == p {
                    proof { assert(!distinct_ports(ports@)); }
                    return false;
                }
                j += 1;
            }
            let mut k = 0;
            while k < self.declarations.len()
                invariant k <= self.declarations.len(), self.wf(),
                    i < ports.len(), p == ports@[i as int],
                    forall|a: int| 0 <= a < k && self.declarations[a].provides && self.nodes[self.declarations[a].owner as int].present
                        ==> self.declarations[a].port != p,
                decreases self.declarations.len() - k,
            {
                let d = self.declarations[k];
                proof {
                    if d.provides && d.port == p && self.nodes[d.owner as int].present {
                        assert(!Self::provision_admissible(self.nodes@, self.declarations@, ports@[i as int]));
                    }
                }
                if d.provides && d.port == p && self.nodes[d.owner].present { return false; }
                k += 1;
            }
            i += 1;
        }
        true
    }

    spec fn declares(declarations: Seq<Declaration>, owner: usize, port: Port, provides: bool) -> bool {
        exists|i: int| 0 <= i < declarations.len() && declarations[i].owner == owner
            && declarations[i].port == port && declarations[i].provides == provides
    }
    spec fn typed_link(declarations: Seq<Declaration>, link: Link) -> bool {
        link.live ==> Self::declares(declarations, link.consumer, Port { key: link.binding.key, realm: link.binding.realm }, false)
            && Self::declares(declarations, link.binding.provider, Port { key: link.binding.key, realm: link.binding.realm }, true)
    }
    proof fn typing_extends(before: Seq<Declaration>, after: Seq<Declaration>, links: Seq<Link>)
        requires before.len() <= after.len(),
            forall|i: int| 0 <= i < before.len() ==> before[i] == after[i],
            forall|i: int| 0 <= i < links.len() ==> Self::typed_link(before, links[i]),
        ensures forall|i: int| 0 <= i < links.len() ==> Self::typed_link(after, links[i]),
    {
        assert forall|i: int| 0 <= i < links.len() implies Self::typed_link(after, links[i]) by {
            if links[i].live {
                let l = links[i];
                let p = Port { key: l.binding.key, realm: l.binding.realm };
                let a = choose|a: int| 0 <= a < before.len() && before[a].owner == l.consumer && before[a].port == p && !before[a].provides;
                let b = choose|b: int| 0 <= b < before.len() && before[b].owner == l.binding.provider && before[b].port == p && before[b].provides;
                assert(after[a] == before[a]);
                assert(after[b] == before[b]);
            }
        }
    }

    spec fn coverage(nodes: Seq<Node>, declarations: Seq<Declaration>, links: Seq<Link>, except: Option<usize>) -> bool {
        forall|i: int| 0 <= i < declarations.len() && !declarations[i].provides
            && nodes[declarations[i].owner as int].present
            && nodes[declarations[i].owner as int].phase != Phase::Inactive
            && except != Some(declarations[i].owner)
            ==> exists|j: int| 0 <= j < links.len() && links[j].live && links[j].consumer == declarations[i].owner
                && links[j].binding.key == declarations[i].port.key && links[j].binding.realm == declarations[i].port.realm
    }
    proof fn coverage_extends(nodes: Seq<Node>, declarations: Seq<Declaration>, before: Seq<Link>, after: Seq<Link>, except: Option<usize>)
        requires Self::coverage(nodes, declarations, before, except), before.len() <= after.len(),
            forall|i: int| 0 <= i < before.len() ==> before[i] == after[i],
        ensures Self::coverage(nodes, declarations, after, except),
    {
        assert forall|i: int| 0 <= i < declarations.len() && !declarations[i].provides
            && nodes[declarations[i].owner as int].present && nodes[declarations[i].owner as int].phase != Phase::Inactive
            && except != Some(declarations[i].owner)
            implies exists|j: int| 0 <= j < after.len() && after[j].live && after[j].consumer == declarations[i].owner
                && after[j].binding.key == declarations[i].port.key && after[j].binding.realm == declarations[i].port.realm by {
            let d = declarations[i];
            let j = choose|j: int| 0 <= j < before.len() && before[j].live && before[j].consumer == d.owner
                && before[j].binding.key == d.port.key && before[j].binding.realm == d.port.realm;
            assert(after[j] == before[j]);
        }
    }
    pub closed spec fn wf(&self) -> bool {
        self.safety_wf() && Self::coverage(self.nodes@, self.declarations@, self.links@, None)
    }

    /// Registry structure and the resource-lifetime invariant, for arbitrary size.
    pub closed spec fn safety_wf(&self) -> bool {
        &&& self.exclusive_provisions()
        &&& Self::link_order(self.links@)
        &&& forall|i: int| 0 <= i < self.links.len() ==> Self::typed_link(self.declarations@, self.links[i])
        &&& forall|i: int| 0 <= i < self.nodes.len() ==> Self::node_ok(self.nodes@, i)
        &&& forall|i: int| 0 <= i < self.declarations.len() ==> self.declarations[i].owner < self.nodes.len()
        &&& forall|i: int| 0 <= i < self.links.len() ==> Self::link_ok(self.nodes@, #[trigger] self.links[i])
    }
    /// Along a live dependency chain, commitment positions strictly decrease.
    /// This excludes installed dependency cycles, even across reactivations.
    spec fn link_order(links: Seq<Link>) -> bool {
        forall|i: int, j: int| 0 <= i < links.len() && 0 <= j < links.len()
            && links[i].live && links[j].live && links[i].binding.provider == links[j].consumer
            ==> j < i
    }
    pub closed spec fn cleanup_enabled(&self, id: usize) -> bool {
        self.registered(id) && self.nodes[id as int].phase == Phase::Unloading
            && !self.nodes[id as int].restoring
            && forall|j: int| 0 <= j < self.links.len() ==> !(self.links[j].live && self.links[j].binding.provider == id)
    }
    pub closed spec fn all_unloading(&self) -> bool {
        forall|i: int| 0 <= i < self.nodes.len() && self.nodes[i].present && self.nodes[i].phase != Phase::Inactive
            ==> self.nodes[i].phase == Phase::Unloading && !self.nodes[i].restoring
    }
    pub closed spec fn has_installed(&self) -> bool {
        exists|i: int| 0 <= i < self.nodes.len() && self.nodes[i].present && self.nodes[i].phase != Phase::Inactive
    }
    proof fn latest_live(links: Seq<Link>) -> (index: int)
        requires exists|i: int| 0 <= i < links.len() && links[i].live,
        ensures 0 <= index < links.len(), links[index].live,
            forall|i: int| index < i < links.len() ==> !links[i].live,
        decreases links.len(),
    {
        if links.last().live { links.len() - 1 } else {
            let i = choose|i: int| 0 <= i < links.len() && links[i].live;
            assert(i < links.len() - 1);
            assert(links.drop_last()[i].live);
            let j = Self::latest_live(links.drop_last());
            assert forall|k: int| j < k < links.len() implies !links[k].live by {
                if k < links.len() - 1 { assert(links.drop_last()[k] == links[k]); }
                else { assert(links[k] == links.last()); }
            }
            j
        }
    }
    /// Dependency guards cannot deadlock a finite, fully unloading registry.
    /// This establishes an enabled cleanup, not termination of user futures.
    pub proof fn draining_can_progress(&self)
        requires self.wf(), self.all_unloading(), self.has_installed(),
        ensures exists|id: usize| self.cleanup_enabled(id),
    {
        if exists|j: int| 0 <= j < self.links.len() && self.links[j].live {
            let j = Self::latest_live(self.links@);
            let id = self.links[j].consumer;
            assert forall|k: int| 0 <= k < self.links.len() implies !(self.links[k].live && self.links[k].binding.provider == id) by {
                if self.links[k].live && self.links[k].binding.provider == id { assert(j < k); }
            }
            assert(self.cleanup_enabled(id));
        } else {
            let i = choose|i: int| 0 <= i < self.nodes.len() && self.nodes[i].present && self.nodes[i].phase != Phase::Inactive;
            assert(self.cleanup_enabled(i as usize));
        }
    }
    /// At most one Active provider can resolve a fixed key/realm port.
    pub proof fn resolution_unique(&self, port: Port, a: usize, b: usize)
        requires self.wf(), self.resolves_to(port, a), self.resolves_to(port, b),
        ensures a == b,
    {
        let i = choose|i: int| 0 <= i < self.declarations.len() && self.declarations[i].provides
            && self.declarations[i].owner == a && self.declarations[i].port == port;
        let j = choose|j: int| 0 <= j < self.declarations.len() && self.declarations[j].provides
            && self.declarations[j].owner == b && self.declarations[j].port == port;
        assert(self.declarations[i].owner == self.declarations[j].owner);
    }
    spec fn node_ok(nodes: Seq<Node>, i: int) -> bool {
        let n = nodes[i];
        &&& (!n.present ==> n.phase == Phase::Inactive && !n.restoring)
        &&& (n.restoring ==> n.phase == Phase::Unloading && n.present)
        &&& (n.present ==> match n.parent {
            Some(p) => p < i && nodes[p as int].present,
            None => true,
        })
    }
    #[verifier::inline]
    spec fn link_ok(nodes: Seq<Node>, l: Link) -> bool {
        l.live ==> {
            &&& l.consumer < nodes.len()
            &&& l.binding.provider < nodes.len()
            &&& nodes[l.consumer as int].present
            &&& nodes[l.consumer as int].phase != Phase::Inactive
            &&& nodes[l.binding.provider as int].present
            &&& nodes[l.binding.provider as int].phase != Phase::Inactive
            &&& !nodes[l.binding.provider as int].restoring
        }
    }
    pub closed spec fn resource_safe(&self, consumer: usize, provider: usize) -> bool {
        (exists|j: int| 0 <= j < self.links.len() && self.links[j].live
            && self.links[j].consumer == consumer && self.links[j].binding.provider == provider)
        ==> provider < self.nodes.len() && self.nodes[provider as int].present
            && self.nodes[provider as int].phase != Phase::Inactive
            && !self.nodes[provider as int].restoring
    }
    pub proof fn ordering(&self, consumer: usize, provider: usize)
        requires self.wf(),
        ensures self.resource_safe(consumer, provider),
    {
        if exists|j: int| 0 <= j < self.links.len() && self.links[j].live
            && self.links[j].consumer == consumer && self.links[j].binding.provider == provider {
            let j = choose|j: int| 0 <= j < self.links.len() && self.links[j].live
                && self.links[j].consumer == consumer && self.links[j].binding.provider == provider;
            assert(Self::link_ok(self.nodes@, self.links[j]));
        }
    }
    pub fn new() -> (r: Self)
        ensures r.wf(), r.next_id() == 0, r.paper().fibers.dom().is_empty(),
    { Self { nodes: Vec::new(), declarations: Vec::new(), links: Vec::new() } }

    pub closed spec fn record_count(&self) -> nat { self.links.len() as nat }
    pub closed spec fn compacted_from(&self, prior: &Self) -> bool {
        self.nodes@ == prior.nodes@ && self.declarations@ == prior.declarations@
            && self.links@ == prior.links@.filter(|l: Link| l.live)
            && self.same_live_bindings(prior) && self.links.len() <= prior.links.len()
            && forall|i: int| 0 <= i < self.links.len() ==> self.links[i].live
    }
    /// Number of stored commitment records, including obsolete episodes.
    pub fn binding_records(&self) -> (count: usize)
        ensures count == self.record_count(),
    { self.links.len() }
    /// Allocated stable identity slots. Removed identities are never reused.
    pub fn identity_slots(&self) -> (count: usize)
        ensures count == self.next_id(),
    { self.nodes.len() }
    pub closed spec fn declaration_count(&self) -> nat { self.declarations.len() as nat }
    pub fn declaration_records(&self) -> (count: usize)
        ensures count == self.declaration_count(),
    { self.declarations.len() }
    pub closed spec fn same_interfaces(&self, other: &Self) -> bool {
        self.nodes@ == other.nodes@ && forall|owner: usize, port: Port, provides: bool| self.registered(owner)
            ==> Self::declares(self.declarations@, owner, port, provides) == Self::declares(other.declarations@, owner, port, provides)
    }
    pub closed spec fn declarations_compacted_from(&self, prior: &Self) -> bool {
        self.declarations@ == prior.declarations@.filter(|d: Declaration| prior.nodes[d.owner as int].present)
    }
    /// Remove declarations belonging to removed identities. All remaining
    /// interfaces, identities, phases and committed bindings are preserved.
    pub fn compact_declarations(&mut self) -> (removed: usize)
        requires old(self).wf(),
        ensures final(self).generations_preserved(old(self)), final(self).wf(), final(self).same_interfaces(old(self)), final(self).same_bindings(old(self)),
            final(self).paper() == old(self).paper(),
            final(self).declarations_compacted_from(old(self)),
            final(self).declaration_count() <= old(self).declaration_count(),
            removed == old(self).declaration_count() - final(self).declaration_count(),
    {
        let ghost keep = |d: Declaration| self.nodes[d.owner as int].present;
        proof { reveal(Seq::filter); }
        let mut kept: Vec<Declaration> = Vec::new();
        let ghost mut positions: Seq<int> = Seq::empty();
        let mut i = 0;
        while i < self.declarations.len()
            invariant i <= self.declarations.len(), self.wf(), self == old(self),
                kept.len() <= i, positions.len() == kept.len(),
                kept@ == self.declarations@.subrange(0, i as int).filter(keep),
                forall|d: Declaration| #[trigger] keep(d) == self.nodes[d.owner as int].present,
                forall|a: int| 0 <= a < kept.len() ==> 0 <= #[trigger] positions[a] < i
                    && kept[a] == self.declarations[positions[a]] && self.registered(kept[a].owner),
                forall|a: int| 0 <= a < i && self.registered(self.declarations[a].owner) ==> positions.contains(a),
            decreases self.declarations.len() - i,
        {
            proof {
                let prefix = self.declarations@.subrange(0, i as int);
                assert(self.declarations@.subrange(0, i + 1) =~= prefix.push(self.declarations[i as int]));
                prefix.lemma_filter_push(self.declarations[i as int], keep);
            }
            let ghost prior_positions = positions;
            if self.nodes[self.declarations[i].owner].present {
                kept.push(self.declarations[i]);
                proof { positions = positions.push(i as int); }
            }
            proof {
                assert forall|a: int| 0 <= a < i + 1 && self.registered(self.declarations[a].owner) implies positions.contains(a) by {
                    if a < i {
                        assert(prior_positions.contains(a));
                        let k = choose|k: int| 0 <= k < prior_positions.len() && prior_positions[k] == a;
                        assert(positions[k] == a);
                    } else { assert(positions[positions.len() - 1] == a); }
                }
            }
            i += 1;
        }
        proof { assert(self.declarations@.subrange(0, i as int) =~= self.declarations@); }
        let removed = self.declarations.len() - kept.len();
        let ghost before = self.declarations@;
        self.declarations = kept;
        proof {
            assert forall|a: int| 0 <= a < self.declarations.len() implies self.declarations[a].owner < self.nodes.len() by {
                assert(self.declarations[a] == before[positions[a]]);
            }
            assert forall|owner: usize, port: Port, provides: bool| self.registered(owner)
                implies Self::declares(self.declarations@, owner, port, provides) == Self::declares(before, owner, port, provides) by {
                if Self::declares(before, owner, port, provides) {
                    let a = choose|a: int| 0 <= a < before.len() && before[a].owner == owner && before[a].port == port && before[a].provides == provides;
                    assert(positions.contains(a));
                    let b = choose|b: int| 0 <= b < positions.len() && positions[b] == a;
                    assert(self.declarations[b] == before[a]);
                }
                if Self::declares(self.declarations@, owner, port, provides) {
                    let b = choose|b: int| 0 <= b < self.declarations.len() && self.declarations[b].owner == owner && self.declarations[b].port == port && self.declarations[b].provides == provides;
                    assert(before[positions[b]] == self.declarations[b]);
                }
            }
            assert forall|i: int, j: int| 0 <= i < self.declarations.len() && 0 <= j < self.declarations.len()
                && self.declarations[i].provides && self.declarations[j].provides
                && self.nodes[self.declarations[i].owner as int].present && self.nodes[self.declarations[j].owner as int].present
                && self.declarations[i].port == self.declarations[j].port implies self.declarations[i].owner == self.declarations[j].owner by {
                assert(before[positions[i]] == self.declarations[i]);
                assert(before[positions[j]] == self.declarations[j]);
            }
            assert forall|i: int| 0 <= i < self.links.len() implies Self::typed_link(self.declarations@, self.links[i]) by {
                let l = self.links[i];
                if l.live {
                    let p = Port { key: l.binding.key, realm: l.binding.realm };
                    assert(Self::declares(self.declarations@, l.consumer, p, false));
                    assert(Self::declares(self.declarations@, l.binding.provider, p, true));
                }
            }
            assert forall|a: int| 0 <= a < self.declarations.len() && !self.declarations[a].provides
                && self.nodes[self.declarations[a].owner as int].present && self.nodes[self.declarations[a].owner as int].phase != Phase::Inactive
                implies exists|j: int| 0 <= j < self.links.len() && self.links[j].live && self.links[j].consumer == self.declarations[a].owner
                    && self.links[j].binding.key == self.declarations[a].port.key && self.links[j].binding.realm == self.declarations[a].port.realm by {
                assert(before[positions[a]] == self.declarations[a]);
            }
        }
        proof { self.paper_stutter(old(self)); }
        removed
    }
    pub closed spec fn same_live_bindings(&self, other: &Self) -> bool {
        forall|id: usize, b: Binding| self.binding_recorded(id, b) == other.binding_recorded(id, b)
    }
    // Keep the local sequence proof separate from the executable filter loop.
    // A retained record must be live; the checked premise rejects an inverted
    // retention condition without entangling it with the final graph proof.
    proof fn compact_bindings_push(links: Seq<Link>, kept: Seq<Link>, positions: Seq<int>, i: int)
        requires 0 <= i < links.len(), links[i].live, positions.len() == kept.len(),
            forall|a: int| 0 <= a < kept.len() ==> 0 <= #[trigger] positions[a] < i
                && kept[a] == links[positions[a]] && kept[a].live,
            forall|a: int, b: int| 0 <= a < b < kept.len() ==> positions[a] < positions[b],
        ensures
            forall|a: int| 0 <= a < kept.push(links[i]).len() ==> 0 <= #[trigger] positions.push(i)[a] < i + 1
                && kept.push(links[i])[a] == links[positions.push(i)[a]] && kept.push(links[i])[a].live,
            forall|a: int, b: int| 0 <= a < b < kept.push(links[i]).len() ==> positions.push(i)[a] < positions.push(i)[b],
    {
        let next_kept = kept.push(links[i]);
        let next_positions = positions.push(i);
        assert forall|a: int| 0 <= a < next_kept.len() implies 0 <= next_positions[a] < i + 1
            && next_kept[a] == links[next_positions[a]] && next_kept[a].live by {
            if a < kept.len() { assert(next_positions[a] == positions[a]); assert(next_kept[a] == kept[a]); }
            else { assert(next_positions[a] == i); assert(next_kept[a] == links[i]); }
        }
        assert forall|a: int, b: int| 0 <= a < b < next_kept.len() implies next_positions[a] < next_positions[b] by {
            if b < positions.len() { assert(positions[a] < positions[b]); }
            else { assert(next_positions[b] == i); assert(positions[a] < i); }
        }
    }
    // Only the completed position map is needed to transport graph invariants
    // and live-binding observations to the compacted sequence.
    proof fn compact_bindings_preserves(&self, prior: &Self, positions: Seq<int>)
        requires prior.wf(), self.nodes@ == prior.nodes@, self.declarations@ == prior.declarations@,
            positions.len() == self.links.len(),
            forall|a: int| 0 <= a < self.links.len() ==> 0 <= #[trigger] positions[a] < prior.links.len()
                && self.links[a] == prior.links[positions[a]] && self.links[a].live,
            forall|a: int, b: int| 0 <= a < b < self.links.len() ==> positions[a] < positions[b],
            forall|a: int| 0 <= a < prior.links.len() && #[trigger] prior.links[a].live ==> positions.contains(a),
        ensures self.wf(), self.same_live_bindings(prior),
    {
        let before = prior.links@;
        assert forall|a: int| 0 <= a < self.links.len() implies self.links[a].live
            && Self::typed_link(self.declarations@, self.links[a]) && Self::link_ok(self.nodes@, self.links[a]) by {
            assert(before[positions[a]] == self.links[a]);
            assert(Self::typed_link(self.declarations@, before[positions[a]]));
            assert(Self::link_ok(self.nodes@, before[positions[a]]));
        }
        assert forall|a: int, b: int| 0 <= a < self.links.len() && 0 <= b < self.links.len()
            && self.links[a].live && self.links[b].live && self.links[a].binding.provider == self.links[b].consumer
            implies b < a by {
            assert(before[positions[a]] == self.links[a]);
            assert(before[positions[b]] == self.links[b]);
            assert(positions[b] < positions[a]);
        }
        assert forall|a: int| 0 <= a < self.declarations.len() && !self.declarations[a].provides
            && self.nodes[self.declarations[a].owner as int].present && self.nodes[self.declarations[a].owner as int].phase != Phase::Inactive
            implies exists|j: int| 0 <= j < self.links.len() && self.links[j].live && self.links[j].consumer == self.declarations[a].owner
                && self.links[j].binding.key == self.declarations[a].port.key && self.links[j].binding.realm == self.declarations[a].port.realm by {
            let d = self.declarations[a];
            let k = choose|k: int| 0 <= k < before.len() && before[k].live && before[k].consumer == d.owner
                && before[k].binding.key == d.port.key && before[k].binding.realm == d.port.realm;
            assert(positions.contains(k));
            let j = choose|j: int| 0 <= j < positions.len() && positions[j] == k;
            assert(self.links[j] == before[k]);
        }
        assert forall|id: usize, b: Binding| self.binding_recorded(id, b) == prior.binding_recorded(id, b) by {
            if prior.binding_recorded(id, b) {
                let k = choose|k: int| 0 <= k < before.len() && before[k].live && before[k].consumer == id && before[k].binding == b;
                assert(positions.contains(k));
                let j = choose|j: int| 0 <= j < positions.len() && positions[j] == k;
                assert(self.links[j] == before[k]);
                assert(self.binding_recorded(id, b));
            }
            if self.binding_recorded(id, b) {
                let j = choose|j: int| 0 <= j < self.links.len() && self.links[j].live && self.links[j].consumer == id && self.links[j].binding == b;
                assert(before[positions[j]] == self.links[j]);
                assert(prior.binding_recorded(id, b));
            }
        }
    }
    /// Reclaim obsolete episode links without changing identities, declarations,
    /// live bindings, or their order. Safe even while consumers are unloading.
    pub fn compact_bindings(&mut self) -> (removed: usize)
        requires old(self).wf(),
        ensures final(self).generations_preserved(old(self)), final(self).wf(), final(self).compacted_from(old(self)), final(self).paper() == old(self).paper(),
            removed == old(self).record_count() - final(self).record_count(),
    {
        let ghost keep = |l: Link| l.live;
        proof { reveal(Seq::filter); }
        let mut kept: Vec<Link> = Vec::new();
        let ghost mut positions: Seq<int> = Seq::empty();
        let mut i = 0;
        while i < self.links.len()
            invariant i <= self.links.len(), self.wf(), self == old(self),
                kept.len() <= i, positions.len() == kept.len(),
                kept@ == self.links@.subrange(0, i as int).filter(keep),
                forall|l: Link| #[trigger] keep(l) == l.live,
                forall|a: int| 0 <= a < kept.len() ==> 0 <= #[trigger] positions[a] < i
                    && kept[a] == self.links[positions[a]] && kept[a].live,
                forall|a: int, b: int| 0 <= a < b < kept.len() ==> positions[a] < positions[b],
                forall|a: int| 0 <= a < i && #[trigger] self.links[a].live ==> positions.contains(a),
            decreases self.links.len() - i,
        {
            proof {
                let prefix = self.links@.subrange(0, i as int);
                assert(self.links@.subrange(0, i + 1) =~= prefix.push(self.links[i as int]));
                prefix.lemma_filter_push(self.links[i as int], keep);
            }
            let ghost prior_positions = positions;
            if self.links[i].live {
                let ghost prior_kept = kept@;
                kept.push(self.links[i]);
                proof {
                    positions = positions.push(i as int);
                    Self::compact_bindings_push(self.links@, prior_kept, prior_positions, i as int);
                }
            }
            proof {
                assert forall|a: int| 0 <= a < i + 1 && self.links[a].live implies positions.contains(a) by {
                    if a < i {
                        assert(prior_positions.contains(a));
                        let k = choose|k: int| 0 <= k < prior_positions.len() && prior_positions[k] == a;
                        assert(positions[k] == a);
                    } else { assert(positions[positions.len() - 1] == a); }
                }
            }
            i += 1;
        }
        proof { assert(self.links@.subrange(0, i as int) =~= self.links@); }
        let removed = self.links.len() - kept.len();
        self.links = kept;
        proof { self.compact_bindings_preserves(old(self), positions); }
        proof { self.paper_stutter(old(self)); }
        removed
    }

    pub fn contains(&self, id: usize) -> (r: bool)
        ensures r == self.registered(id),
    { id < self.nodes.len() && self.nodes[id].present }

    pub fn phase(&self, id: usize) -> (r: Option<Phase>)
        ensures r == self.phase_of(id),
    {
        if self.contains(id) { Some(self.nodes[id].phase) } else { None }
    }
    pub fn retired(&self, id: usize) -> (r: bool)
        ensures r == self.is_retired(id),
    {
        self.contains(id) && self.nodes[id].retired
    }
    pub fn cleanup_started(&self, id: usize) -> (r: bool)
        ensures r == self.is_restoring(id),
    {
        self.contains(id) && self.nodes[id].restoring
    }
    pub fn ids(&self) -> (r: Vec<usize>) {
        let mut out = Vec::new();
        let mut i = 0;
        while i < self.nodes.len()
            invariant i <= self.nodes.len(),
            decreases self.nodes.len() - i,
        {
            if self.nodes[i].present { out.push(i); }
            i += 1;
        }
        out
    }
    pub fn children(&self, id: usize) -> (r: Vec<usize>) {
        let mut out = Vec::new();
        let mut i = 0;
        while i < self.nodes.len()
            invariant i <= self.nodes.len(),
            decreases self.nodes.len() - i,
        {
            if self.nodes[i].present && self.nodes[i].parent == Some(id) { out.push(i); }
            i += 1;
        }
        out
    }

    // A single checked mutation gate. It checks exactly the incident bindings
    // and registry references affected by this node; it does not assume safety.
    fn update_node(&mut self, id: usize, node: Node) -> (r: Result<(), Error>)
        requires old(self).safety_wf(),
        ensures r != Err(Error::Changed), final(self).safety_wf(), final(self).declarations@ == old(self).declarations@,
            final(self).same_bindings(old(self)),
            final(self).nodes.len() == old(self).nodes.len(),
            r.is_ok() ==> final(self).nodes@ == old(self).nodes@.update(id as int, node),
            r.is_err() ==> final(self).unchanged(old(self)),
            r.is_ok() ==> final(self).nodes_frame(old(self), id),
            old(self).registered(id) && node.present && !node.restoring && node.phase != Phase::Inactive
                && node.parent == old(self).nodes[id as int].parent ==> r.is_ok(),
            old(self).registered(id) && node.present && node.restoring && node.phase == Phase::Unloading
                && node.parent == old(self).nodes[id as int].parent
                && (forall|j: int| 0 <= j < old(self).links.len()
                    ==> !(old(self).links[j].live && old(self).links[j].binding.provider == id)) ==> r.is_ok(),
            r.is_ok() && !node.present ==> forall|m: int| 0 <= m < old(self).nodes.len()
                ==> !(old(self).nodes[m].present && old(self).nodes[m].parent == Some(id)),
    {
        if id >= self.nodes.len() || !self.nodes[id].present { return Err(Error::Unknown); }
        assert(Self::node_ok(self.nodes@,id as int));
        if (!node.present && (node.phase != Phase::Inactive || node.restoring))
            || (node.restoring && (node.phase != Phase::Unloading || !node.present)) {
            return Err(Error::InvalidState);
        }
        if node.present {
            if let Some(p) = node.parent {
                if p >= id || !self.nodes[p].present { return Err(Error::Unknown); }
            }
        }
        let mut j = 0;
        while j < self.nodes.len()
            invariant j <= self.nodes.len(), self.safety_wf(), id < self.nodes.len(),
                !node.present ==> forall|k: int| 0 <= k < j ==> !(self.nodes[k].present && self.nodes[k].parent == Some(id)),
            decreases self.nodes.len() - j,
        {
            if !node.present && self.nodes[j].present && self.nodes[j].parent == Some(id) {
                return Err(Error::Children);
            }
            j += 1;
        }
        let mut k = 0;
        while k < self.links.len()
            invariant k <= self.links.len(), self.safety_wf(), id < self.nodes.len(),
                forall|a: int| 0 <= a < k && #[trigger] self.links[a].live ==> {
                    &&& (self.links[a].consumer == id ==> node.present && node.phase != Phase::Inactive)
                    &&& (self.links[a].binding.provider == id ==> node.present && node.phase != Phase::Inactive && !node.restoring)
                },
            decreases self.links.len() - k,
        {
            let l = self.links[k];
            if l.live {
                if l.consumer == id && (!node.present || node.phase == Phase::Inactive) { return Err(Error::Relied); }
                if l.binding.provider == id && (!node.present || node.phase == Phase::Inactive || node.restoring) { return Err(Error::Relied); }
            }
            proof {
                assert forall|a: int| 0 <= a < k + 1 && #[trigger] self.links[a].live implies {
                    &&& (self.links[a].consumer == id ==> node.present && node.phase != Phase::Inactive)
                    &&& (self.links[a].binding.provider == id ==> node.present && node.phase != Phase::Inactive && !node.restoring)
                } by {
                    if a == k { assert(self.links[a] == l); }
                }
            }
            k += 1;
        }
        let ghost prior = self.nodes@;
        self.nodes.set(id, node);
        proof {
            assert forall|a: int| 0 <= a < self.nodes.len() implies Self::node_ok(self.nodes@, a) by {
                assert(Self::node_ok(prior, a));
            }
        }
        Ok(())
    }

    pub closed spec fn same_control(&self, prior: &Self) -> bool {
        self.nodes@ == prior.nodes@
    }
    pub closed spec fn declares_provision(&self, owner: usize, port: Port) -> bool {
        Self::declares(self.declarations@, owner, port, true)
    }

    /// Extend a live logical fiber's service interface, including its initial
    /// inactive reservation before the first Begin. Admission of host effects
    /// to that reservation is the host's responsibility. This is a host extension
    /// beyond the paper's fixed-interface Insert rule. It preserves the kernel
    /// resource invariant and does not allocate an artificial provider fiber.
    /// Revoking a host value does not release this reservation. The host may
    /// release it explicitly after all committed references to this port drain.
    pub fn declare_provision(&mut self, owner: usize, port: Port) -> (r: Result<(), Error>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).generations_preserved(old(self)),
            final(self).same_control(old(self)),
            final(self).same_bindings(old(self)),
            r.is_ok() ==> final(self).declares_provision(owner, port),
            r.is_err() ==> final(self).unchanged(old(self)),
    {
        if !self.contains(owner) { return Err(Error::Unknown); }
        if self.nodes[owner].retired { return Err(Error::Retired); }
        if self.nodes[owner].phase != Phase::Loading && self.nodes[owner].phase != Phase::Active
            && !(self.nodes[owner].phase == Phase::Inactive && self.nodes[owner].generation == 0) {
            return Err(Error::InvalidState);
        }
        let mut i = 0;
        while i < self.declarations.len()
            invariant i <= self.declarations.len(), self.wf(), self == old(self),
                owner < self.nodes.len(),
                forall|j: int| 0 <= j < i && self.declarations[j].provides
                    && self.nodes[self.declarations[j].owner as int].present
                    && self.declarations[j].port == port ==> self.declarations[j].owner == owner,
            decreases self.declarations.len() - i,
        {
            let declaration = self.declarations[i];
            if declaration.provides && declaration.port == port
                && self.nodes[declaration.owner].present {
                if declaration.owner == owner { return Ok(()); }
                return Err(Error::Conflict);
            }
            i += 1;
        }
        if self.declarations.len() == usize::MAX { return Err(Error::Capacity); }
        let ghost previous = self.declarations@;
        self.declarations.push(Declaration { owner, port, provides: true });
        proof {
            assert(self.declarations[previous.len() as int] == Declaration { owner, port, provides: true });
            assert(Self::declares(self.declarations@, owner, port, true));
            Self::typing_extends(previous, self.declarations@, self.links@);
            assert forall|a: int, b: int| 0 <= a < self.declarations.len() && 0 <= b < self.declarations.len()
                && self.declarations[a].provides && self.declarations[b].provides
                && self.nodes[self.declarations[a].owner as int].present
                && self.nodes[self.declarations[b].owner as int].present
                && self.declarations[a].port == self.declarations[b].port
                implies self.declarations[a].owner == self.declarations[b].owner by {
                if a < previous.len() && b < previous.len() {
                    assert(previous[a] == self.declarations[a]);
                    assert(previous[b] == self.declarations[b]);
                }
            }
        }
        Ok(())
    }

    /// Whether this logical fiber still reserves a port, in any control phase.
    pub fn provision_reserved(&self, owner: usize, port: Port) -> (reserved: bool)
        ensures reserved == self.declares_provision(owner, port),
    {
        let mut i = 0;
        while i < self.declarations.len()
            invariant i <= self.declarations.len(),
                forall|j: int| 0 <= j < i ==> !(self.declarations[j].provides
                    && self.declarations[j].owner == owner && self.declarations[j].port == port),
            decreases self.declarations.len() - i,
        {
            let d = self.declarations[i];
            if d.provides && d.owner == owner && d.port == port { return true; }
            i += 1;
        }
        false
    }

    pub closed spec fn provision_released_from(&self, prior: &Self, owner: usize, port: Port) -> bool {
        self.nodes@ == prior.nodes@ && self.links@ == prior.links@
            && self.declarations@ == prior.declarations@.filter(
                |d: Declaration| !(d.provides && d.owner == owner && d.port == port))
    }

    pub closed spec fn other_interfaces_preserved(&self, prior: &Self, owner: usize, port: Port) -> bool {
        forall|n: usize, p: Port, provides: bool| !(provides && n == owner && p == port)
            ==> Self::declares(self.declarations@, n, p, provides) == Self::declares(prior.declarations@, n, p, provides)
    }

    /// Release a port reservation without removing the logical fiber. This is
    /// a host extension of the paper's fixed interfaces, not a paper Step.
    /// Every committed reference to this owner/port must have finished cleanup
    /// first. Other ports, all commitments and the owner's episode are unchanged.
    /// Publication revocation and value leases remain the host registry's duty.
    // Keep this quantified filtering proof independent of other root-module queries.
    #[verifier::spinoff_prover]
    pub fn release_provision(&mut self, owner: usize, port: Port) -> (r: Result<(), Error>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).generations_preserved(old(self)),
            final(self).same_control(old(self)), final(self).same_bindings(old(self)),
            r.is_err() ==> final(self).unchanged(old(self)),
            r.is_ok() ==> final(self).provision_released_from(old(self), owner, port)
                && !final(self).declares_provision(owner, port),
            r.is_ok() ==> final(self).other_interfaces_preserved(old(self), owner, port),
    {
        if !self.contains(owner) { return Err(Error::Unknown); }
        let mut k = 0;
        while k < self.links.len()
            invariant k <= self.links.len(), self.wf(), self == old(self),
                forall|j: int| 0 <= j < k ==> !(self.links[j].live
                    && self.links[j].binding.provider == owner
                    && self.links[j].binding.key == port.key && self.links[j].binding.realm == port.realm),
            decreases self.links.len() - k,
        {
            let l = self.links[k];
            if l.live && l.binding.provider == owner && l.binding.key == port.key && l.binding.realm == port.realm {
                return Err(Error::Relied);
            }
            k += 1;
        }
        let ghost keep = |d: Declaration| !(d.provides && d.owner == owner && d.port == port);
        proof { reveal(Seq::filter); }
        let mut kept: Vec<Declaration> = Vec::new();
        let ghost mut positions: Seq<int> = Seq::empty();
        let mut i = 0;
        while i < self.declarations.len()
            invariant i <= self.declarations.len(), self.wf(), self == old(self),
                forall|j: int| 0 <= j < self.links.len() ==> !(self.links[j].live
                    && self.links[j].binding.provider == owner
                    && self.links[j].binding.key == port.key && self.links[j].binding.realm == port.realm),
                kept.len() <= i, positions.len() == kept.len(),
                kept@ == self.declarations@.subrange(0, i as int).filter(keep),
                forall|d: Declaration| #[trigger] keep(d) == !(d.provides && d.owner == owner && d.port == port),
                forall|a: int| 0 <= a < kept.len() ==> 0 <= #[trigger] positions[a] < i
                    && kept[a] == self.declarations[positions[a]] && keep(kept[a]),
                forall|a: int| 0 <= a < i && keep(self.declarations[a]) ==> positions.contains(a),
            decreases self.declarations.len() - i,
        {
            proof {
                let prefix = self.declarations@.subrange(0, i as int);
                assert(self.declarations@.subrange(0, i + 1) =~= prefix.push(self.declarations[i as int]));
                prefix.lemma_filter_push(self.declarations[i as int], keep);
            }
            let ghost prior_positions = positions;
            let d = self.declarations[i];
            if !(d.provides && d.owner == owner && d.port == port) {
                kept.push(d);
                proof { positions = positions.push(i as int); }
            }
            proof {
                assert forall|a: int| 0 <= a < i + 1 && keep(self.declarations[a]) implies positions.contains(a) by {
                    if a < i {
                        assert(prior_positions.contains(a));
                        let b = choose|b: int| 0 <= b < prior_positions.len() && prior_positions[b] == a;
                        assert(positions[b] == a);
                    } else { assert(positions[positions.len() - 1] == a); }
                }
            }
            i += 1;
        }
        proof { assert(self.declarations@.subrange(0, i as int) =~= self.declarations@); }
        let ghost before = self.declarations@;
        self.declarations = kept;
        proof {
            assert forall|a: int| 0 <= a < self.declarations.len() implies self.declarations[a].owner < self.nodes.len() by {
                assert(self.declarations[a] == before[positions[a]]);
            }
            assert forall|n: usize, p: Port, provides: bool| !(provides && n == owner && p == port)
                implies Self::declares(self.declarations@, n, p, provides) == Self::declares(before, n, p, provides) by {
                if Self::declares(before, n, p, provides) {
                    let a = choose|a: int| 0 <= a < before.len() && before[a].owner == n && before[a].port == p && before[a].provides == provides;
                    assert(positions.contains(a));
                    let b = choose|b: int| 0 <= b < positions.len() && positions[b] == a;
                    assert(self.declarations[b] == before[a]);
                }
                if Self::declares(self.declarations@, n, p, provides) {
                    let b = choose|b: int| 0 <= b < self.declarations.len() && self.declarations[b].owner == n && self.declarations[b].port == p && self.declarations[b].provides == provides;
                    assert(before[positions[b]] == self.declarations[b]);
                }
            }
            assert forall|a: int, b: int| 0 <= a < self.declarations.len() && 0 <= b < self.declarations.len()
                && self.declarations[a].provides && self.declarations[b].provides
                && self.nodes[self.declarations[a].owner as int].present && self.nodes[self.declarations[b].owner as int].present
                && self.declarations[a].port == self.declarations[b].port implies self.declarations[a].owner == self.declarations[b].owner by {
                assert(before[positions[a]] == self.declarations[a]);
                assert(before[positions[b]] == self.declarations[b]);
            }
            assert forall|j: int| 0 <= j < self.links.len() implies Self::typed_link(self.declarations@, self.links[j]) by {
                let l = self.links[j];
                if l.live {
                    let p = Port { key: l.binding.key, realm: l.binding.realm };
                    assert(Self::declares(self.declarations@, l.consumer, p, false));
                    assert(Self::declares(self.declarations@, l.binding.provider, p, true));
                }
            }
            assert forall|a: int| 0 <= a < self.declarations.len() && !self.declarations[a].provides
                && self.nodes[self.declarations[a].owner as int].present && self.nodes[self.declarations[a].owner as int].phase != Phase::Inactive
                implies exists|j: int| 0 <= j < self.links.len() && self.links[j].live && self.links[j].consumer == self.declarations[a].owner
                    && self.links[j].binding.key == self.declarations[a].port.key && self.links[j].binding.realm == self.declarations[a].port.realm by {
                assert(before[positions[a]] == self.declarations[a]);
            }
        }
        Ok(())
    }

    pub closed spec fn pending_dependencies_configured(&self, prior: &Self, id: usize, dependencies: Seq<Port>) -> bool {
        &&& self.nodes@ == prior.nodes@ && self.links@ == prior.links@
        &&& forall|p: Port| Self::declares(self.declarations@, id, p, false) == dependencies.contains(p)
        &&& forall|n: usize, p: Port, provides: bool| n != id || provides
            ==> Self::declares(self.declarations@, n, p, provides) == Self::declares(prior.declarations@, n, p, provides)
    }

    /// Seal-time dependency configuration for a reserved, never-started fiber.
    /// This preserves its stable identity so synchronous mount observers can
    /// change injection before admission. Configuration after begin is rejected.
    /// The host extension preserves safety but is not the paper's Insert rule.
    pub fn configure_pending_dependencies(&mut self, id: usize, dependencies: Vec<Port>) -> (r: Result<(), Error>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).generations_preserved(old(self)),
            final(self).same_control(old(self)), final(self).same_bindings(old(self)),
            r.is_err() ==> final(self).unchanged(old(self)),
            r.is_ok() ==> final(self).pending_dependencies_configured(old(self), id, dependencies@),
    {
        if !self.contains(id) { return Err(Error::Unknown); }
        if self.nodes[id].retired { return Err(Error::Retired); }
        if self.nodes[id].phase != Phase::Inactive || self.nodes[id].generation != 0 {
            return Err(Error::InvalidState);
        }
        if dependencies.len() > usize::MAX - self.declarations.len() { return Err(Error::Capacity); }
        let mut a = 0;
        while a < dependencies.len()
            invariant a <= dependencies.len(), self.wf(), self == old(self),
            decreases dependencies.len() - a,
        {
            let mut b = 0;
            while b < a
                invariant b <= a, a < dependencies.len(), self.wf(), self == old(self),
                decreases a - b,
            {
                if dependencies[a] == dependencies[b] { return Err(Error::Conflict); }
                b += 1;
            }
            a += 1;
        }
        let mut kept: Vec<Declaration> = Vec::new();
        let ghost mut positions: Seq<int> = Seq::empty();
        let mut i = 0;
        while i < self.declarations.len()
            invariant i <= self.declarations.len(), self.wf(), self == old(self),
                id < self.nodes.len(), self.nodes[id as int].phase == Phase::Inactive,
                kept.len() <= i, positions.len() == kept.len(),
                forall|a: int| 0 <= a < kept.len() ==> 0 <= #[trigger] positions[a] < i
                    && kept[a] == self.declarations[positions[a]] && (kept[a].owner != id || kept[a].provides),
                forall|a: int| 0 <= a < i && (self.declarations[a].owner != id || self.declarations[a].provides) ==> positions.contains(a),
            decreases self.declarations.len() - i,
        {
            let ghost prior_positions = positions;
            let d = self.declarations[i];
            if d.owner != id || d.provides {
                kept.push(d);
                proof { positions = positions.push(i as int); }
            }
            proof {
                assert forall|a: int| 0 <= a < i + 1 && (self.declarations[a].owner != id || self.declarations[a].provides)
                    implies positions.contains(a) by {
                    if a < i {
                        assert(prior_positions.contains(a));
                        let b = choose|b: int| 0 <= b < prior_positions.len() && prior_positions[b] == a;
                        assert(positions[b] == a);
                    } else { assert(positions[positions.len() - 1] == a); }
                }
            }
            i += 1;
        }
        let ghost before = self.declarations@;
        self.declarations = kept;
        proof {
            assert forall|a: int| 0 <= a < self.declarations.len() implies self.declarations[a].owner < self.nodes.len() by {
                assert(self.declarations[a] == before[positions[a]]);
            }
            assert forall|n: usize, p: Port, provides: bool| n != id || provides
                implies Self::declares(self.declarations@, n, p, provides) == Self::declares(before, n, p, provides) by {
                if Self::declares(before, n, p, provides) {
                    let a = choose|a: int| 0 <= a < before.len() && before[a].owner == n && before[a].port == p && before[a].provides == provides;
                    assert(positions.contains(a));
                    let b = choose|b: int| 0 <= b < positions.len() && positions[b] == a;
                    assert(self.declarations[b] == before[a]);
                }
                if Self::declares(self.declarations@, n, p, provides) {
                    let b = choose|b: int| 0 <= b < self.declarations.len() && self.declarations[b].owner == n && self.declarations[b].port == p && self.declarations[b].provides == provides;
                    assert(before[positions[b]] == self.declarations[b]);
                }
            }
            assert forall|a: int, b: int| 0 <= a < self.declarations.len() && 0 <= b < self.declarations.len()
                && self.declarations[a].provides && self.declarations[b].provides
                && self.nodes[self.declarations[a].owner as int].present && self.nodes[self.declarations[b].owner as int].present
                && self.declarations[a].port == self.declarations[b].port implies self.declarations[a].owner == self.declarations[b].owner by {
                assert(before[positions[a]] == self.declarations[a]);
                assert(before[positions[b]] == self.declarations[b]);
            }
            assert forall|j: int| 0 <= j < self.links.len() implies Self::typed_link(self.declarations@, self.links[j]) by {
                let l = self.links[j];
                if l.live {
                    assert(Self::link_ok(self.nodes@, l));
                    assert(l.consumer != id);
                    let p = Port { key: l.binding.key, realm: l.binding.realm };
                    assert(Self::declares(self.declarations@, l.consumer, p, false));
                    assert(Self::declares(self.declarations@, l.binding.provider, p, true));
                }
            }
            assert forall|a: int| 0 <= a < self.declarations.len() && !self.declarations[a].provides
                && self.nodes[self.declarations[a].owner as int].present && self.nodes[self.declarations[a].owner as int].phase != Phase::Inactive
                implies exists|j: int| 0 <= j < self.links.len() && self.links[j].live && self.links[j].consumer == self.declarations[a].owner
                    && self.links[j].binding.key == self.declarations[a].port.key && self.links[j].binding.realm == self.declarations[a].port.realm by {
                assert(before[positions[a]] == self.declarations[a]);
            }
            assert(self.wf());
        }
        proof {
            assert forall|a: int| 0 <= a < self.declarations.len()
                implies self.declarations[a].owner != id || self.declarations[a].provides by {
                assert(self.declarations[a] == before[positions[a]]);
            }
        }
        let ghost retained = self.declarations@;
        let mut i = 0;
        while i < dependencies.len()
            invariant i <= dependencies.len(), self.wf(), self.nodes@ == old(self).nodes@, self.links@ == old(self).links@,
                id < self.nodes.len(), self.nodes[id as int].phase == Phase::Inactive,
                self.declarations.len() == retained.len() + i,
                forall|a: int| 0 <= a < retained.len() ==> self.declarations[a] == retained[a]
                    && (retained[a].owner != id || retained[a].provides),
                forall|a: int| 0 <= a < i ==> self.declarations[retained.len() + a] == (Declaration { owner: id, port: dependencies[a], provides: false }),
                forall|n: usize, p: Port, provides: bool| n != id || provides
                    ==> Self::declares(self.declarations@, n, p, provides) == Self::declares(old(self).declarations@, n, p, provides),
            decreases dependencies.len() - i,
        {
            let ghost previous = self.declarations@;
            self.declarations.push(Declaration { owner: id, port: dependencies[i], provides: false });
            proof {
                Self::typing_extends(previous, self.declarations@, self.links@);
                assert forall|n: usize, p: Port, provides: bool| n != id || provides
                    implies Self::declares(self.declarations@, n, p, provides) == Self::declares(old(self).declarations@, n, p, provides) by {
                    if Self::declares(self.declarations@, n, p, provides) {
                        let j = choose|j: int| 0 <= j < self.declarations.len() && self.declarations[j].owner == n && self.declarations[j].port == p && self.declarations[j].provides == provides;
                        assert(j < previous.len());
                    }
                    if Self::declares(old(self).declarations@, n, p, provides) {
                        let j = choose|j: int| 0 <= j < previous.len() && previous[j].owner == n && previous[j].port == p && previous[j].provides == provides;
                        assert(self.declarations[j] == previous[j]);
                    }
                }
            }
            i += 1;
        }
        proof {
            assert forall|p: Port| Self::declares(self.declarations@, id, p, false) == dependencies@.contains(p) by {
                if Self::declares(self.declarations@, id, p, false) {
                    let j = choose|j: int| 0 <= j < self.declarations.len() && self.declarations[j].owner == id && self.declarations[j].port == p && !self.declarations[j].provides;
                    if j < retained.len() {
                        assert(self.declarations[j] == retained[j]);
                        assert(retained[j].owner != id || retained[j].provides);
                    }
                    assert(j >= retained.len());
                    assert(dependencies[j - retained.len()] == p);
                }
                if dependencies@.contains(p) {
                    let j = choose|j: int| 0 <= j < dependencies.len() && dependencies[j] == p;
                    assert(self.declarations[retained.len() + j] == (Declaration { owner: id, port: p, provides: false }));
                }
            }
        }
        Ok(())
    }

    /// Check the actual insertion domain without allocating an identity or
    /// reserving a port. The result describes this state only; insert repeats
    /// these same checks, so an intervening registration can invalidate it.
    pub fn check_insert(&self, parent: Option<usize>, dependencies: &[Port], provisions: &[Port]) -> (r: Result<(), Error>)
        requires self.wf(),
        ensures r.is_ok() == self.insert_enabled(parent, dependencies@, provisions@),
            (r == Err(Error::Capacity)) == (self.next_id() == usize::MAX),
            (r == Err(Error::Unknown)) == (self.next_id() < usize::MAX
                && parent.is_some() && !self.registered(parent.unwrap())),
            (r == Err(Error::Conflict)) == (self.next_id() < usize::MAX
                && (parent.is_some() ==> self.registered(parent.unwrap()))
                && (!self.provisions_available(provisions@) || !distinct_ports(dependencies@))),
    {
        if self.nodes.len() == usize::MAX { return Err(Error::Capacity); }
        if let Some(p) = parent {
            if !self.contains(p) { return Err(Error::Unknown); }
        }
        if !self.check_provisions(provisions) { return Err(Error::Conflict); }
        let mut d = 0;
        while d < dependencies.len()
            invariant d <= dependencies.len(), self.next_id() < usize::MAX,
                (parent.is_some() ==> self.registered(parent.unwrap())), self.provisions_available(provisions@),
                forall|a: int, b: int| 0 <= a < b < d ==> dependencies@[a] != dependencies@[b],
            decreases dependencies.len() - d,
        {
            let mut j = 0;
            while j < d
                invariant j <= d, d < dependencies.len(), self.next_id() < usize::MAX,
                (parent.is_some() ==> self.registered(parent.unwrap())), self.provisions_available(provisions@),
                    forall|a: int| 0 <= a < j ==> dependencies@[a] != dependencies@[d as int],
                decreases d - j,
            {
                if dependencies[j] == dependencies[d] {
                    proof { assert(!distinct_ports(dependencies@)); }
                    return Err(Error::Conflict);
                }
                j += 1;
            }
            d += 1;
        }
        Ok(())
    }

    #[verifier::rlimit(30)]
    pub fn insert(&mut self, parent: Option<usize>, dependencies: Vec<Port>, provisions: Vec<Port>) -> (r: Result<usize, Error>)
        requires old(self).wf(),
        ensures final(self).generations_preserved(old(self)), final(self).wf(),
            r.is_ok() == old(self).insert_enabled(parent, dependencies@, provisions@),
            r.is_ok() ==> r.unwrap() == old(self).next_id()
                && final(self).next_id() == old(self).next_id() + 1
                && final(self).phase_of(r.unwrap()) == Some(Phase::Inactive)
                && !final(self).is_retired(r.unwrap())
                && refinement::step(old(self).paper(), final(self).paper(), r.unwrap(), refinement::Rule::Insert)
                && final(self).paper().fibers[r.unwrap()].parent == parent
                && (forall|p: Port| final(self).paper().fibers[r.unwrap()].dependencies.contains(p) == dependencies@.contains(p))
                && (forall|p: Port| final(self).paper().fibers[r.unwrap()].provisions.contains(p) == provisions@.contains(p)),
            r.is_err() ==> final(self).unchanged(old(self)),
    {
        self.check_insert(parent, dependencies.as_slice(), provisions.as_slice())?;
        let ghost initial_declarations = self.declarations@;
        let ghost initial_nodes = self.nodes@;
        let id = self.nodes.len();
        let ghost prior = self.nodes@;
        self.nodes.push(Node { present: true, retired: false, phase: Phase::Inactive, restoring: false, parent, generation:0 });
        proof {
            assert forall|a: int| 0 <= a < self.nodes.len() implies Self::node_ok(self.nodes@, a) by {
                if a < id { assert(Self::node_ok(prior, a)); }
            }
        }
        let ghost created = self.nodes@;
        let mut i = 0;
        while i < dependencies.len()
            invariant old(self).insert_enabled(parent, dependencies@, provisions@), i <= dependencies.len(), self.wf(), id < self.nodes.len(), self.nodes@ == created, self.nodes[id as int].phase == Phase::Inactive,
                self.links@ == old(self).links@,
                self.declarations.len() == initial_declarations.len() + i,
                forall|a: int| 0 <= a < i ==> self.declarations[initial_declarations.len() + a] == (Declaration { owner: id, port: dependencies[a], provides: false }),
                initial_nodes.len() < self.nodes.len(),
                forall|a: int| 0 <= a < initial_nodes.len() ==> self.nodes[a] == initial_nodes[a],
                initial_declarations.len() <= self.declarations.len(),
                forall|a: int| 0 <= a < initial_declarations.len() ==> initial_declarations[a].owner < initial_nodes.len(),
                forall|a: int| 0 <= a < initial_declarations.len() ==> self.declarations[a] == initial_declarations[a],
                forall|a: int| initial_declarations.len() <= a < self.declarations.len() ==> !self.declarations[a].provides,
                forall|a: int| 0 <= a < provisions.len() ==> Self::provision_admissible(initial_nodes, initial_declarations, provisions[a]),
            decreases dependencies.len() - i,
        {
            let ghost previous = self.declarations@;
            self.declarations.push(Declaration { owner: id, port: dependencies[i], provides: false });
            proof { Self::typing_extends(previous, self.declarations@, self.links@); }
            i += 1;
        }
        let mut i = 0;
        while i < provisions.len()
            invariant old(self).insert_enabled(parent, dependencies@, provisions@), i <= provisions.len(), self.wf(), id < self.nodes.len(), self.nodes@ == created, self.nodes[id as int].phase == Phase::Inactive,
                self.links@ == old(self).links@,
                self.declarations.len() == initial_declarations.len() + dependencies.len() + i,
                forall|a: int| 0 <= a < dependencies.len() ==> self.declarations[initial_declarations.len() + a] == (Declaration { owner: id, port: dependencies[a], provides: false }),
                forall|a: int| 0 <= a < i ==> self.declarations[initial_declarations.len() + dependencies.len() + a] == (Declaration { owner: id, port: provisions[a], provides: true }),
                initial_nodes.len() < self.nodes.len(),
                forall|a: int| 0 <= a < initial_nodes.len() ==> self.nodes[a] == initial_nodes[a],
                initial_declarations.len() <= self.declarations.len(),
                forall|a: int| 0 <= a < initial_declarations.len() ==> initial_declarations[a].owner < initial_nodes.len(),
                forall|a: int| 0 <= a < initial_declarations.len() ==> self.declarations[a] == initial_declarations[a],
                forall|a: int| initial_declarations.len() <= a < self.declarations.len() && self.declarations[a].provides ==> self.declarations[a].owner == id,
                forall|a: int| 0 <= a < provisions.len() ==> Self::provision_admissible(initial_nodes, initial_declarations, provisions[a]),
                initial_nodes.len() < self.nodes.len(),
                forall|a: int| 0 <= a < initial_nodes.len() ==> self.nodes[a] == initial_nodes[a],
            decreases provisions.len() - i,
        {
            proof { assert(Self::provision_admissible(initial_nodes, initial_declarations, provisions[i as int])); }
            let ghost previous = self.declarations@;
            proof { assert(Self::unique_provisions(self.nodes@, previous)); }
            self.declarations.push(Declaration { owner: id, port: provisions[i], provides: true });
            proof {
                Self::typing_extends(previous, self.declarations@, self.links@);
                assert forall|a: int, b: int| 0 <= a < self.declarations.len() && 0 <= b < self.declarations.len()
                    && self.declarations[a].provides && self.declarations[b].provides
                    && self.nodes[self.declarations[a].owner as int].present
                    && self.nodes[self.declarations[b].owner as int].present
                    && self.declarations[a].port == self.declarations[b].port
                    implies self.declarations[a].owner == self.declarations[b].owner by {
                    if a < previous.len() && b < previous.len() {
                        assert(previous[a] == self.declarations[a]);
                        assert(previous[b] == self.declarations[b]);
                    } else if a == previous.len() && b < initial_declarations.len() {
                        assert(initial_declarations[b].port != provisions[i as int]);
                    } else if b == previous.len() && a < initial_declarations.len() {
                        assert(initial_declarations[a].port != provisions[i as int]);
                    }
                }
            }
            i += 1;
        }
        proof {
            assert(self.nodes_frame(old(self), id));
            assert forall|n: usize, p: Port, provides: bool| n != id && self.registered(n)
                implies Self::declares(self.declarations@, n, p, provides) == Self::declares(initial_declarations, n, p, provides) by {
                if Self::declares(self.declarations@, n, p, provides) {
                    let j = choose|j: int| 0 <= j < self.declarations.len() && self.declarations[j].owner == n && self.declarations[j].port == p && self.declarations[j].provides == provides;
                    if j >= initial_declarations.len() {
                        if j < initial_declarations.len() + dependencies.len() {
                            assert(self.declarations[initial_declarations.len() + (j - initial_declarations.len())] == (Declaration { owner: id, port: dependencies[j - initial_declarations.len()], provides: false }));
                        } else {
                            assert(self.declarations[initial_declarations.len() + dependencies.len() + (j - initial_declarations.len() - dependencies.len())] == (Declaration { owner: id, port: provisions[j - initial_declarations.len() - dependencies.len()], provides: true }));
                        }
                    }
                    assert(initial_declarations[j] == self.declarations[j]);
                }
                if Self::declares(initial_declarations, n, p, provides) {
                    let j = choose|j: int| 0 <= j < initial_declarations.len() && initial_declarations[j].owner == n && initial_declarations[j].port == p && initial_declarations[j].provides == provides;
                    assert(initial_declarations[j] == self.declarations[j]);
                }
            }
            self.paper_frame(old(self), id);
            assert(self.paper_fiber(id).committed.is_empty());
            assert forall|m: usize, p: Port| refinement::registered(old(self).paper(), m) && old(self).paper().fibers[m].provisions.contains(p)
                implies !self.paper().fibers[id].provisions.contains(p) by {
                let a = choose|a: int| 0 <= a < initial_declarations.len() && initial_declarations[a].owner == m && initial_declarations[a].port == p && initial_declarations[a].provides;
                if self.paper_fiber(id).provisions.contains(p) {
                    let b = choose|b: int| 0 <= b < self.declarations.len() && self.declarations[b].owner == id && self.declarations[b].port == p && self.declarations[b].provides;
                    assert(self.declarations[a] == initial_declarations[a]);
                    assert(self.declarations[a].owner == self.declarations[b].owner);
                }
            }
            assert forall|p: Port| self.paper_fiber(id).dependencies.contains(p) == dependencies@.contains(p) by {
                if self.paper_fiber(id).dependencies.contains(p) {
                    let j = choose|j: int| 0 <= j < self.declarations.len() && self.declarations[j].owner == id && self.declarations[j].port == p && !self.declarations[j].provides;
                    if j < initial_declarations.len() { assert(self.declarations[j] == initial_declarations[j]); }
                    if j >= initial_declarations.len() + dependencies.len() {
                        let k = j - initial_declarations.len() - dependencies.len();
                        assert(0 <= k < provisions.len());
                        assert(self.declarations[initial_declarations.len() + dependencies.len() + k] == (Declaration { owner: id, port: provisions[k], provides: true }));
                    }
                    assert(initial_declarations.len() <= j < initial_declarations.len() + dependencies.len());
                    assert(dependencies[j - initial_declarations.len()] == p);
                }
                if dependencies@.contains(p) {
                    let j = choose|j: int| 0 <= j < dependencies.len() && dependencies[j] == p;
                    assert(self.declarations[initial_declarations.len() + j].port == p);
                }
            }
            assert forall|p: Port| self.paper_fiber(id).provisions.contains(p) == provisions@.contains(p) by {
                if self.paper_fiber(id).provisions.contains(p) {
                    let j = choose|j: int| 0 <= j < self.declarations.len() && self.declarations[j].owner == id && self.declarations[j].port == p && self.declarations[j].provides;
                    if j < initial_declarations.len() { assert(self.declarations[j] == initial_declarations[j]); }
                    if initial_declarations.len() <= j < initial_declarations.len() + dependencies.len() {
                        let k = j - initial_declarations.len();
                        assert(0 <= k < dependencies.len());
                        assert(self.declarations[initial_declarations.len() + k] == (Declaration { owner: id, port: dependencies[k], provides: false }));
                    }
                    assert(initial_declarations.len() + dependencies.len() <= j);
                    assert(provisions[j - initial_declarations.len() - dependencies.len()] == p);
                }
                if provisions@.contains(p) {
                    let j = choose|j: int| 0 <= j < provisions.len() && provisions[j] == p;
                    assert(self.declarations[initial_declarations.len() + dependencies.len() + j].port == p);
                }
            }
        }
        Ok(id)
    }

    pub fn resolve(&self, port: Port) -> (r: Option<usize>)
        requires self.wf(),
        ensures r.is_some() ==> self.resolves_to(port, r.unwrap()),
            r.is_none() ==> !self.has_provider(port),
    {
        let mut i = 0;
        while i < self.declarations.len()
            invariant i <= self.declarations.len(), self.wf(),
                forall|j: int| 0 <= j < i ==> !(self.declarations[j].provides && self.declarations[j].port == port
                    && self.active_provider(self.declarations[j].owner)),
            decreases self.declarations.len() - i,
        {
            let d = self.declarations[i];
            if d.provides && d.port == port && self.nodes[d.owner].present && self.nodes[d.owner].phase == Phase::Active {
                proof {
                    assert(Self::node_ok(self.nodes@, d.owner as int));
                    assert(!self.nodes[d.owner as int].restoring);
                    assert(self.active_provider(d.owner));
                    assert(self.resolves_to(port, d.owner));
                }
                return Some(d.owner);
            }
            proof {
                assert(Self::node_ok(self.nodes@, d.owner as int));
            }
            i += 1;
        }
        None
    }

    pub fn target(&self, id: usize) -> (r: Option<Vec<Binding>>)
        requires self.wf(),
        ensures r.is_some() ==> self.complete_target(id, r.unwrap()@),
            r.is_none() ==> self.unavailable(id),
    {
        if !self.contains(id) || self.nodes[id].retired { return None; }
        let mut out: Vec<Binding> = Vec::new();
        let mut i = 0;
        while i < self.declarations.len()
            invariant i <= self.declarations.len(), self.wf(), self.registered(id), !self.nodes[id as int].retired,
                forall|j: int| 0 <= j < out.len() ==> self.binding_is_target(id, #[trigger] out[j]),
                forall|j: int| 0 <= j < i && !self.declarations[j].provides && self.declarations[j].owner == id
                    ==> Self::view_has_port(out@, self.declarations[j].port),
            decreases self.declarations.len() - i,
        {
            let ghost prev = out@;
            let d = self.declarations[i];
            if !d.provides && d.owner == id {
                match self.resolve(d.port) {
                    Some(provider) => {
                        let binding = Binding { key: d.port.key, realm: d.port.realm, provider };
                        proof { assert(self.binding_is_target(id, binding)); }
                        out.push(binding);
                        proof { assert(out[prev.len() as int] == binding); assert(Self::view_has_port(out@, d.port)); }
                    },
                    None => { proof { assert(self.unavailable(id)); } return None; },
                }
            }
            proof {
                assert forall|j: int| 0 <= j < i + 1 && !self.declarations[j].provides && self.declarations[j].owner == id
                    implies Self::view_has_port(out@, self.declarations[j].port) by {
                    if j < i {
                        assert(Self::view_has_port(prev, self.declarations[j].port));
                        let k = choose|k: int| 0 <= k < prev.len() && prev[k].key == self.declarations[j].port.key && prev[k].realm == self.declarations[j].port.realm;
                        assert(out[k] == prev[k]);
                    }
                }
            }
            i += 1;
        }
        Some(out)
    }

    pub fn committed(&self, id: usize) -> (out: Vec<Binding>)
        ensures forall|j: int| 0 <= j < out.len() ==> self.binding_recorded(id, out[j]),
            self.all_bindings_in(id, out@),
            self.registered(id) ==> self.paper().fibers[id].committed == ISet::new(|b: Binding| out@.contains(b)),
    {
        let mut out = Vec::new();
        let mut i = 0;
        while i < self.links.len()
            invariant i <= self.links.len(),
                forall|j: int| 0 <= j < out.len() ==> self.binding_recorded(id, #[trigger] out[j]),
                forall|j: int| 0 <= j < i && self.links[j].live && self.links[j].consumer == id
                    ==> out@.contains(self.links[j].binding),
            decreases self.links.len() - i,
        {
            let ghost prev = out@;
            if self.links[i].live && self.links[i].consumer == id {
                proof { assert(self.binding_recorded(id, self.links[i as int].binding)); }
                out.push(self.links[i].binding);
                proof {
                    assert(out[prev.len() as int] == self.links[i as int].binding);
                    assert(out@.contains(self.links[i as int].binding));
                }
            }
            proof {
                assert forall|j: int| 0 <= j < i + 1 && self.links[j].live && self.links[j].consumer == id
                    implies out@.contains(self.links[j].binding) by {
                    if j < i {
                        assert(prev.contains(self.links[j].binding));
                        let k = choose|k: int| 0 <= k < prev.len() && prev[k] == self.links[j].binding;
                        assert(out[k] == prev[k]);
                    }
                }
            }
            i += 1;
        }
        proof {
            if self.registered(id) {
                assert(self.paper().fibers[id].committed =~= ISet::new(|b: Binding| out@.contains(b))) by {
                    assert forall|b: Binding| self.paper().fibers[id].committed.contains(b) == out@.contains(b) by {
                        if out@.contains(b) {
                            let j = choose|j: int| 0 <= j < out.len() && out[j] == b;
                            assert(self.binding_recorded(id, out[j]));
                        }
                        if self.binding_recorded(id, b) {
                            let j = choose|j: int| 0 <= j < self.links.len() && self.links[j].live && self.links[j].consumer == id && self.links[j].binding == b;
                            assert(out@.contains(self.links[j].binding));
                        }
                    }
                }
            }
        }
        out
    }

    pub fn begin(&mut self, id: usize) -> (r: Result<(), Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
            r.is_ok() == old(self).begin_enabled(id),
            r.is_ok() ==> final(self).iteration_enabled(id),
            r.is_ok() ==> old(self).generation_of(id).is_some() && final(self).generation_of(id).is_some()
                && final(self).generation_of(id).unwrap() as nat == old(self).generation_of(id).unwrap() as nat + 1,
            forall|n:usize| n != id ==> final(self).generation_of(n) == old(self).generation_of(n), final(self).next_id() == old(self).next_id(),
 r.is_ok() ==> final(self).committed_from(old(self), id),
            r.is_ok() ==> final(self).phase_of(id) == Some(Phase::Loading)
                && refinement::step(old(self).paper(), final(self).paper(), id, refinement::Rule::Begin),
            r.is_err() ==> final(self).unchanged(old(self)),
    {
        if !self.contains(id) { return Err(Error::Unknown); }
        let mut node = self.nodes[id];
        if node.phase != Phase::Inactive { return Err(Error::InvalidState); }
        if node.retired { return Err(Error::Retired); }
        if node.generation == u64::MAX { return Err(Error::Capacity); }
        let bindings = match self.target(id) { Some(b) => b, None => return Err(Error::MissingDependency) };
        proof {
            assert forall|j: int| 0 <= j < self.declarations.len() && !self.declarations[j].provides
                && self.declarations[j].owner == id implies self.has_provider(self.declarations[j].port) by {
                let p = self.declarations[j].port;
                let k = choose|k: int| 0 <= k < bindings.len() && bindings[k].key == p.key && bindings[k].realm == p.realm;
                assert(self.binding_is_target(id, bindings[k]));
                assert(self.resolves_to(p, bindings[k].provider));
            }
            assert(old(self).begin_enabled(id));
            assert(Self::node_ok(self.nodes@, id as int));
        }
        let ghost before = self.nodes@;
        node.phase = Phase::Loading;
        node.generation += 1;
        self.update_node(id, node)?;
        let mut i = 0;
        while i < bindings.len()
            invariant i <= bindings.len(), self.safety_wf(), old(self).wf(), old(self).begin_enabled(id),
                self.nodes@ == before.update(id as int, node),
                before == old(self).nodes@,
                self.nodes_frame(old(self), id),
                self.links.len() >= old(self).links.len(),
                forall|j: int| 0 <= j < old(self).links.len() ==> self.links[j] == old(self).links[j],
                forall|j: int| old(self).links.len() <= j < self.links.len() ==> self.links[j].consumer == id,
                forall|j: int| 0 <= j < self.links.len() && self.links[j].live ==> self.links[j].binding.provider != id,
                forall|j: int| 0 <= j < bindings.len() ==> bindings[j].provider != id,
                Self::coverage(self.nodes@, self.declarations@, self.links@, Some(id)), id < self.nodes.len(),
                self.nodes[id as int].present, self.nodes[id as int].phase == Phase::Loading,
                old(self).complete_target(id, bindings@), self.declarations@ == old(self).declarations@,
                forall|j: int| 0 <= j < self.links.len() && self.links[j].live && self.links[j].consumer == id
                    ==> old(self).binding_is_target(id, self.links[j].binding),
                forall|j: int| 0 <= j < i ==> self.binding_recorded(id, #[trigger] bindings[j]),
                forall|j: int| 0 <= j < bindings.len() ==> {
                    let p = #[trigger] bindings[j].provider;
                    &&& p < self.nodes.len()
                    &&& self.nodes[p as int].present
                    &&& self.nodes[p as int].phase != Phase::Inactive
                    &&& !self.nodes[p as int].restoring
                },
            decreases bindings.len() - i,
        {
            let ghost previous = self.links@;
            proof {
                let b = bindings[i as int];
                assert(old(self).binding_is_target(id, b));
                assert(Self::typed_link(self.declarations@, Link { consumer: id, binding: b, live: true }));
            }
            self.links.push(Link { consumer: id, binding: bindings[i], live: true });
            proof {
                Self::coverage_extends(self.nodes@, self.declarations@, previous, self.links@, Some(id));
                assert(self.links[previous.len() as int].binding == bindings[i as int]);
                assert forall|j: int| 0 <= j < i + 1 implies self.binding_recorded(id, #[trigger] bindings[j]) by {
                    if j < i {
                        let k = choose|k: int| 0 <= k < previous.len() && previous[k].live
                            && previous[k].consumer == id && previous[k].binding == bindings[j];
                        assert(self.links[k] == previous[k]);
                    }
                }
            }
            i += 1;
        }
        proof {
            // The binding loop only appends links. Discharge the episode
            // metadata frame separately from the quantified service proof.
            assert(self.generation_of(id) == Some(node.generation));
            assert(node.generation as nat == old(self).generation_of(id).unwrap() as nat + 1);
            assert forall|n: usize| n != id implies self.generation_of(n) == old(self).generation_of(n) by {
                assert(self.registered(n) == old(self).registered(n));
                if self.registered(n) { assert(self.nodes[n as int] == old(self).nodes[n as int]); }
            }
        }
        proof {
            assert forall|j: int| 0 <= j < old(self).declarations.len() && !old(self).declarations[j].provides && old(self).declarations[j].owner == id
                implies exists|k: int| 0 <= k < self.links.len() && self.links[k].live && self.links[k].consumer == id
                    && self.links[k].binding.key == old(self).declarations[j].port.key && self.links[k].binding.realm == old(self).declarations[j].port.realm by {
                let d = old(self).declarations[j];
                assert(Self::view_has_port(bindings@, d.port));
                let k = choose|k: int| 0 <= k < bindings.len() && bindings[k].key == d.port.key && bindings[k].realm == d.port.realm;
                assert(self.binding_recorded(id, bindings[k]));
            }
        }
        proof {
            assert forall|n: usize, b: Binding| n != id implies self.binding_recorded(n, b) == old(self).binding_recorded(n, b) by {
                if self.binding_recorded(n, b) {
                    let j = choose|j: int| 0 <= j < self.links.len() && self.links[j].live && self.links[j].consumer == n && self.links[j].binding == b;
                    assert(j < old(self).links.len());
                    assert(self.links[j] == old(self).links[j]);
                }
                if old(self).binding_recorded(n, b) {
                    let j = choose|j: int| 0 <= j < old(self).links.len() && old(self).links[j].live && old(self).links[j].consumer == n && old(self).links[j].binding == b;
                    assert(self.links[j] == old(self).links[j]);
                }
            }
            self.paper_frame(old(self), id);
            self.paper_target(old(self), id);
            assert(self.paper_fiber(id).dependencies =~= old(self).paper_fiber(id).dependencies);
            assert(self.paper_fiber(id).provisions =~= old(self).paper_fiber(id).provisions);
        }
        proof {
            refinement::begin_preserves_target(old(self).paper(), self.paper(), id);
            self.paper_iteration_guard(id);
        }
        Ok(())
    }

    /// Validate the paper's Loading/coherent guard. The existing uniqueness,
    /// typing and coverage invariants make an available target agree with every
    /// installed commitment, independent of private vector order/multiplicity.
    /// A stage already admitted by the host may still land after this is false.
    pub fn check_iteration(&self, id: usize) -> (r: Result<(), Error>)
        requires self.wf(),
        ensures r.is_ok() == self.iteration_enabled(id),
            r.is_ok() ==> self.phase_of(id) == Some(Phase::Loading) && self.coherent(id)
                && refinement::step(self.paper(), self.paper(), id, refinement::Rule::Iter),
    {
        if !self.contains(id) { return Err(Error::Unknown); }
        if self.nodes[id].phase != Phase::Loading { return Err(Error::InvalidState); }
        let _target = match self.target(id) {
            Some(target) => target,
            None => {
                proof { self.paper_coherence(id); self.unavailable_not_coherent(id); }
                return Err(Error::Changed);
            },
        };
        proof {
            self.refines_paper();
            self.paper_target_vector(id, _target@);
            refinement::available_installed_coherent(self.paper(), id, ISet::new(|b: Binding| _target@.contains(b)));
            self.paper_coherence(id);
        }
        Ok(())
    }

    pub fn finish(&mut self, id: usize) -> (r: Result<(), Error>)
        requires old(self).wf(),
        ensures final(self).generations_preserved(old(self)), final(self).wf(), final(self).next_id() == old(self).next_id(),
 final(self).same_bindings(old(self)),
            r.is_ok() == old(self).iteration_enabled(id),
            r.is_ok() ==> old(self).coherent(id),
            r.is_ok() ==> final(self).phase_of(id) == Some(Phase::Active)
                && refinement::step(old(self).paper(), final(self).paper(), id, refinement::Rule::Finish),
            r.is_err() ==> final(self).unchanged(old(self)),
    {
        self.check_iteration(id)?;
        assert(Self::node_ok(self.nodes@, id as int));
        let ghost prior = *self;
        let mut node = self.nodes[id];
        node.phase = Phase::Active;
        let result = self.update_node(id, node);
        proof { if result.is_ok() {
            self.paper_phase_change(&prior, id, Phase::Active);
            prior.paper_target(&prior, id);
        } }
        result
    }

    pub fn leave(&mut self, id: usize) -> (r: Result<(), Error>)
        requires old(self).wf(),
        ensures final(self).generations_preserved(old(self)), r != Err(Error::Changed), final(self).wf(), final(self).next_id() == old(self).next_id(), final(self).same_bindings(old(self)),
            r.is_ok() ==> final(self).phase_of(id) == Some(Phase::Unloading)
                && refinement::step(old(self).paper(), final(self).paper(), id, refinement::Rule::Restart)
                && (!refinement::coherent(old(self).paper(), id) ==> refinement::step(old(self).paper(), final(self).paper(), id,
                    if old(self).phase_of(id) == Some(Phase::Loading) { refinement::Rule::Divert } else { refinement::Rule::Leave })),
            r.is_err() ==> final(self).unchanged(old(self)),
            r.is_err() ==> !old(self).registered(id)
                || (old(self).phase_of(id) != Some(Phase::Loading) && old(self).phase_of(id) != Some(Phase::Active)),
    {
        if !self.contains(id) { return Err(Error::Unknown); }
        let mut node = self.nodes[id];
        if node.phase != Phase::Loading && node.phase != Phase::Active { return Err(Error::InvalidState); }
        assert(Self::node_ok(self.nodes@,id as int));
        let ghost prior = *self;
        node.phase = Phase::Unloading;
        let result = self.update_node(id, node);
        proof { if result.is_ok() { self.paper_phase_change(&prior, id, Phase::Unloading); } }
        result
    }
    /// The paper's reactive L-Divert/L-Leave rules, with an executable guard.
    /// Explicit cancellation/restart uses `leave` instead.
    pub fn leave_if_changed(&mut self, id: usize) -> (r: Result<(), Error>)
        requires old(self).wf(),
        ensures final(self).generations_preserved(old(self)), final(self).wf(), final(self).next_id() == old(self).next_id(),
            old(self).phase_of(id) == Some(Phase::Loading) || old(self).phase_of(id) == Some(Phase::Active) ==> r.is_ok() || r == Err(Error::Changed),

            r.is_ok() ==> refinement::step(old(self).paper(), final(self).paper(), id,
                if old(self).phase_of(id) == Some(Phase::Loading) { refinement::Rule::Divert } else { refinement::Rule::Leave }),
            r.is_err() ==> final(self).unchanged(old(self)),
            r == Err(Error::Changed) ==> refinement::coherent(old(self).paper(), id),
            r.is_err() ==> r == Err(Error::Changed) || !old(self).registered(id)
                || (old(self).phase_of(id) != Some(Phase::Loading) && old(self).phase_of(id) != Some(Phase::Active)),
    {
        if !self.contains(id) { return Err(Error::Unknown); }
        if self.nodes[id].phase != Phase::Loading && self.nodes[id].phase != Phase::Active {
            return Err(Error::InvalidState);
        }
        if let Some(_bindings) = self.target(id) {
            proof {
                self.refines_paper();
                self.paper_target_vector(id, _bindings@);
                refinement::available_installed_coherent(self.paper(), id, ISet::new(|b: Binding| _bindings@.contains(b)));
            }
            return Err(Error::Changed);
        }
        proof { self.unavailable_not_coherent(id); }
        self.leave(id)
    }
    pub proof fn unavailable_not_coherent(&self, id: usize)
        requires self.wf(), self.unavailable(id),
        ensures !refinement::coherent(self.paper(), id),
    {
        if self.registered(id) && !self.is_retired(id) {
            let i = choose|i: int| 0 <= i < self.declarations.len() && !self.declarations[i].provides
                && self.declarations[i].owner == id && !self.has_provider(self.declarations[i].port);
            let p = self.declarations[i].port;
            assert(self.paper_fiber(id).dependencies.contains(p));
            if refinement::coherent(self.paper(), id) {
                let b = choose|b: Binding| self.paper_fiber(id).committed.contains(b) && b.key == p.key && b.realm == p.realm;
                assert(refinement::publishes(self.paper(), p, b.provider));
                let d = choose|d: int| 0 <= d < self.declarations.len() && self.declarations[d].provides
                    && self.declarations[d].owner == b.provider && self.declarations[d].port == p;
                assert(Self::node_ok(self.nodes@, b.provider as int));
                assert(self.active_provider(b.provider));
                assert(self.has_provider(p));
            }
        }
    }
    pub fn retire(&mut self, id: usize) -> (r: Result<(), Error>)
        requires old(self).wf(),
        ensures final(self).generations_preserved(old(self)), final(self).wf(), final(self).next_id() == old(self).next_id(),
            forall|n:usize| final(self).is_restoring(n) == old(self).is_restoring(n),
 final(self).same_bindings(old(self)),
            r.is_ok() == old(self).registered(id),
            r.is_ok() ==> final(self).is_retired(id) && final(self).phase_of(id) == old(self).phase_of(id)
                && refinement::step(old(self).paper(), final(self).paper(), id, refinement::Rule::Retire),
            r.is_err() ==> final(self).unchanged(old(self)),
    {
        if !self.contains(id) { return Err(Error::Unknown); }
        let ghost prior = *self;
        let mut node = self.nodes[id];
        node.retired = true;
        self.nodes.set(id, node);
        let result = Ok(());
        proof { if result.is_ok() {
            assert(self.links@ == prior.links@);
            assert forall|i: int| 0 <= i < self.nodes.len() implies Self::node_ok(self.nodes@, i) by {
                assert(Self::node_ok(prior.nodes@, i));
            }
            assert forall|i: int| 0 <= i < self.links.len() implies Self::link_ok(self.nodes@, self.links[i]) by {
                assert(Self::link_ok(prior.nodes@, prior.links[i]));
            }
            assert(Self::unique_provisions(self.nodes@, self.declarations@));
            assert(Self::coverage(self.nodes@, self.declarations@, self.links@, None));

            assert forall|n: usize, b: Binding| self.binding_recorded(n, b) == prior.binding_recorded(n, b) by { }

            self.paper_frame(&prior, id);
            assert(self.paper_fiber(id).dependencies =~= prior.paper_fiber(id).dependencies);
            assert(self.paper_fiber(id).provisions =~= prior.paper_fiber(id).provisions);
            assert(self.paper_fiber(id).committed =~= prior.paper_fiber(id).committed);
        } }
        result
    }
    pub fn begin_cleanup(&mut self, id: usize) -> (r: Result<(), Error>)
        requires old(self).wf(),
        ensures final(self).generations_preserved(old(self)), final(self).wf(), final(self).next_id() == old(self).next_id(),
            r.is_ok() == old(self).cleanup_enabled(id),
            r.is_ok() ==> final(self).is_restoring(id),
 final(self).same_bindings(old(self)),
            r.is_ok() ==> final(self).restoration_guarded(id),
            final(self).paper() == old(self).paper(),
            r.is_err() ==> final(self).unchanged(old(self)),
    {
        if !self.contains(id) { return Err(Error::Unknown); }
        let mut node = self.nodes[id];
        if node.phase != Phase::Unloading || node.restoring { return Err(Error::InvalidState); }
        let ghost prior = *self;
        node.restoring = true;
        let result = self.update_node(id, node);
        proof {
            if result.is_ok() {
                assert forall|j: int| 0 <= j < prior.links.len()
                    implies !(prior.links[j].live && prior.links[j].binding.provider == id) by {
                    assert(Self::link_ok(self.nodes@, self.links[j]));
                }
                self.paper_frame(&prior, id);
                assert(self.paper_fiber(id).dependencies =~= prior.paper_fiber(id).dependencies);
                assert(self.paper_fiber(id).provisions =~= prior.paper_fiber(id).provisions);
                assert(self.paper_fiber(id).committed =~= prior.paper_fiber(id).committed);
                assert(self.paper_fiber(id).parent == prior.paper_fiber(id).parent);
                assert(self.paper_fiber(id).retired == prior.paper_fiber(id).retired);
                assert(self.paper_fiber(id).phase == prior.paper_fiber(id).phase);
                assert(self.paper_fiber(id) == prior.paper_fiber(id));
                assert(self.paper().fibers =~= prior.paper().fibers) by {
                    assert forall|n: usize| self.registered(n) implies self.paper().fibers[n] == prior.paper().fibers[n] by {
                        if n == id { assert(self.paper_fiber(n) == prior.paper_fiber(n)); }
                        else {
                            assert(refinement::registered(self.paper(), n));
                            assert(refinement::registered(prior.paper(), n));
                            assert(prior.paper().fibers[n] == self.paper().fibers[n]);
                        }
                    }
                }
            } else {
                self.paper_stutter(&prior);
            }
        }
        result
    }
    pub fn finish_cleanup(&mut self, id: usize) -> (r: Result<(), Error>)
        requires old(self).wf(),
        ensures final(self).generations_preserved(old(self)), final(self).wf(), final(self).next_id() == old(self).next_id(),
            r.is_ok() == old(self).is_restoring(id),

            r.is_ok() ==> final(self).phase_of(id) == Some(Phase::Inactive) && final(self).no_committed(id)
                && refinement::step(old(self).paper(), final(self).paper(), id, refinement::Rule::Unload),
            r.is_err() ==> final(self).unchanged(old(self)),
            final(self).commitments_frame(old(self),id),
    {
        if !self.contains(id) { return Err(Error::Unknown); }
        let mut node = self.nodes[id];
        if !node.restoring { return Err(Error::InvalidState); }
        let ghost prior = *self;
        let mut i = 0;
        while i < self.links.len()
            invariant i <= self.links.len(), self.safety_wf(),
                self.nodes@ == prior.nodes@, self.declarations@ == prior.declarations@, prior.wf(),
                self.links.len() == prior.links.len(),
                forall|j: int| 0 <= j < self.links.len() ==> self.links[j].consumer == prior.links[j].consumer
                    && (self.links[j].consumer != id ==> self.links[j] == prior.links[j]),
                Self::coverage(self.nodes@, self.declarations@, self.links@, Some(id)), id < self.nodes.len(),
                self.nodes[id as int].restoring,
                forall|j: int| 0 <= j < i ==> !(self.links[j].live && self.links[j].consumer == id),
            decreases self.links.len() - i,
        {
            let ghost previous = self.links@;
            let mut l = self.links[i];
            if l.consumer == id {
                l.live = false;
                self.links.set(i, l);
            }
            proof {
                assert forall|a: int| 0 <= a < self.declarations.len() && !self.declarations[a].provides
                    && self.nodes[self.declarations[a].owner as int].present && self.nodes[self.declarations[a].owner as int].phase != Phase::Inactive
                    && Some(id) != Some(self.declarations[a].owner)
                    implies exists|j: int| 0 <= j < self.links.len() && self.links[j].live && self.links[j].consumer == self.declarations[a].owner
                        && self.links[j].binding.key == self.declarations[a].port.key && self.links[j].binding.realm == self.declarations[a].port.realm by {
                    let d = self.declarations[a];
                    let j = choose|j: int| 0 <= j < previous.len() && previous[j].live && previous[j].consumer == d.owner
                        && previous[j].binding.key == d.port.key && previous[j].binding.realm == d.port.realm;
                    assert(self.links[j] == previous[j]);
                }
            }
            i += 1;
        }
        node.phase = Phase::Inactive;
        node.restoring = false;
        let ghost before = self.nodes@;
        self.nodes.set(id, node);
        proof {
            assert forall|a: int| 0 <= a < self.nodes.len() implies Self::node_ok(self.nodes@, a) by {
                assert(Self::node_ok(before, a));
            }
        }
        proof {
            self.links_preserve_other_commitments(&prior, id);
            self.paper_frame(&prior, id);
            assert(self.paper_fiber(id).dependencies =~= prior.paper_fiber(id).dependencies);
            assert(self.paper_fiber(id).provisions =~= prior.paper_fiber(id).provisions);
            assert(self.paper_fiber(id).committed.is_empty());
            assert(refinement::registered(prior.paper(), id));
            assert(refinement::registered(self.paper(), id));
            assert(Self::node_ok(prior.nodes@, id as int));
            assert(prior.paper_fiber(id).phase == Phase::Unloading);
            assert(self.paper_fiber(id).phase == Phase::Inactive);
            assert(self.paper_fiber(id).parent == prior.paper_fiber(id).parent);
            assert(self.paper_fiber(id).retired == prior.paper_fiber(id).retired);
            assert(!refinement::relied(prior.paper(), id)) by {
                if refinement::relied(prior.paper(), id) {
                    let (m, b) = choose|pair: (usize, Binding)| refinement::registered(prior.paper(), pair.0)
                        && pair.0 != id && prior.paper().fibers[pair.0].phase != Phase::Inactive
                        && prior.paper().fibers[pair.0].committed.contains(pair.1) && pair.1.provider == id;
                    let j = choose|j: int| 0 <= j < prior.links.len() && prior.links[j].live
                        && prior.links[j].consumer == m && prior.links[j].binding == b;
                    assert(Self::link_ok(prior.nodes@, prior.links[j]));
                }
            }
        }
        proof { assert(refinement::step(prior.paper(), self.paper(), id, refinement::Rule::Unload)); }
        Ok(())
    }
    pub fn remove(&mut self, id: usize) -> (r: Result<(), Error>)
        requires old(self).wf(),
        ensures final(self).generations_preserved(old(self)), final(self).wf(), final(self).next_id() == old(self).next_id(),
 final(self).same_bindings(old(self)),
            r.is_ok() ==> !final(self).registered(id)
                && refinement::step(old(self).paper(), final(self).paper(), id, refinement::Rule::Remove),
            r.is_err() ==> final(self).unchanged(old(self)),
    {
        if !self.contains(id) { return Err(Error::Unknown); }
        let mut node = self.nodes[id];
        if !node.retired { return Err(Error::InvalidState); }
        if node.phase != Phase::Inactive { return Err(Error::InvalidState); }
        let ghost prior = *self;
        node.present = false;
        let result = self.update_node(id, node);
        proof { if result.is_ok() {
            self.paper_frame(&prior, id);
            assert(prior.paper_fiber(id).committed.is_empty()) by {
                assert forall|b: Binding| !prior.paper_fiber(id).committed.contains(b) by {
                    if prior.binding_recorded(id, b) {
                        let j = choose|j: int| 0 <= j < prior.links.len() && prior.links[j].live && prior.links[j].consumer == id && prior.links[j].binding == b;
                        assert(Self::link_ok(prior.nodes@, prior.links[j]));
                    }
                }
            }
        } }
        result
    }
}
} // verus!

pub mod isolated_deletion;

pub mod strict_journal;

pub mod unload_orchestration;

pub mod rewrite_confluence;

pub mod shared_replay;

pub mod shared_execution;

pub mod mixed_iteration_exchange;

pub mod entangled_loading;

pub mod mixed_observational_runs;

pub mod mixed_observational_transport;

pub mod foreign_unload;

pub mod fresh_grammar;

pub mod external_inputs;

pub mod fresh_semantics;

pub mod allocation_inputs;

pub mod fresh_equivariance;

pub mod shared_unload_execution;

pub mod guarded_child_domains;

pub mod selective_foreign_recovery;

pub mod providing_owner_deletion;

pub mod providing_owner_execution;

pub mod providing_owner_transport;

pub mod providing_owner_examples;

pub mod strict_batch_recovery;

pub mod orchestration_support_cycle;

pub mod old_receipt_support;

pub mod old_journal_unload;

pub mod old_journal_closure;

pub mod old_journal_examples;

pub mod old_journal_closed_example;

pub mod paper_invariants;

pub mod observational_permutation;

pub mod functional_quotient;

pub mod old_journal_interleaving;

pub mod old_journal_interleaving_example;

pub mod mixed_age_unload;

pub mod mixed_age_unload_example;

pub mod old_provision_support;

pub mod configuration_entry;

pub mod resolution_completion_counterexample;

pub mod old_provision_journal;

pub mod old_provision_journal_example;

pub mod internal_old_unload;

pub mod internal_old_unload_example;

pub mod effect_realization;

pub mod foreign_provision_transport;

pub mod internal_table_unload;

pub mod internal_table_unload_example;

pub mod generalized_table_deletion;

pub mod generalized_table_deletion_example;

pub mod interface_observation;

pub mod interface_observation_example;

pub mod dependent_independence;

pub mod dependent_independence_example;

pub mod dynamic_table_registry;

pub mod dynamic_table_registry_example;

pub mod dynamic_table_deletion;

pub mod dynamic_table_deletion_example;

pub mod strict_partial_quotient;

pub mod strict_partial_quotient_reflexive;

pub mod strict_partial_quotient_example;

pub mod strict_partial_quotient_per;

pub mod strict_partial_quotient_boundary;

pub mod paper_components;

pub mod paper_observations;

pub mod paper_confinement;

pub mod foreign_child_transport;

pub mod foreign_child_transport_example;

pub mod paper_typed_context;

pub mod paper_instantiation;

pub mod mixed_foreign_restore;

pub mod foreign_child_deletion;

pub mod foreign_child_deletion_example;

pub mod paper_trace_independence;

#[cfg(test)]
mod iteration_tests;
