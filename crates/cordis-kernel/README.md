# cordis-kernel

Executable Rust lifecycle and reversible-resource primitives verified with
[Verus](https://github.com/verus-lang/verus). The same source is compiled by
Cargo; ghost contracts are erased in ordinary builds.

This independent, experimental implementation follows Cordis lifecycle semantics:
provider identity, episode-committed bindings, restoration guards, LIFO inverse
stacks, stage admission/landing, and witnessed resource journals. Concrete
operations simulate an independent paper control model. Conditional proofs cover
finite-history normalization, quiet control-state uniqueness, no-deadlock and
step-count bounds. An owned `driver::Driver` connects concrete resource rollback
to provider guards; `ownership::ChildEpisode` captures real child retirement
witnesses. `semantics` models value-carrying tables and iterator results. This is
not an official Cordis distribution.

The fixed `program::ProgramDriver` interprets immutable bounded programs using
actual resource witnesses and Kernel guards, with checked port layouts and total
publication. Additional proof modules cover algebra, observational/renaming
simulation, primitive full-rule preservation, dynamic schedule uniqueness and
constructive fixed-registry termination. The paper inventory records the exact
scope; these results do not establish whole-lifecycle confluence.

Dependent grammar proofs include per-operation argument and outcome types,
strict partial inverses and arbitrary continuation indices. Their actual finite-context
families now derive complete strict monoid/continuation independence for unrelated
I/J indices and different outcome carriers, without enumerating indices. The partial
full-State interpreter derives receipt provenance and successful-step safety,
then constructs one total model from stable actual-call history. A dependent
full-state interpretation retains arbitrary continuation indices and proves
finite-context projection, definedness and recursive witnesses. Historical
ordering proofs cover provider lifetimes, frozen commitments and actual
operation origins. Frozen state-map/edit factorization preserves rule frames.
Checked child handles capture a nonreused episode generation within the same
Kernel instance. An owning ChildDriver scans real journals to prevent removal
of referenced children and atomically diverts landings after target drift.
A unified mathematical dependent/child interpretation now preserves typed safety,
original-index receipts and retained child identities through all nine rules.
Ordering follows actual operation inverses through child retirement states.
Definition 42 uses greatest-bisimulation continuations and observational inverse
comparison. A diagonal proof bounds the unrestricted set/function reading of
Definition 28. Closed mixed/fresh-program drivers construct actual histories,
including authentic inverse journals and single-admission landing. Arbitrary
callbacks and asynchronous host refinement remain open. Actual Begin/Unload
traces derive observational value recovery under explicit scalar laws; separate
constructive deletion profiles prove legal surviving lifecycle executions. The
module contracts retain their registry, domain and interference conditions.
All table landings, including new foreign Provision, now compose with arbitrary-age
internal table cleanup and dynamic foreign Insert/Remove in the private-owner profile.
Actual source guards and local dependency separation derive all target steps;
historical entries survive removal with their original input and receipt. Local function
observations lift to all keys using explicit forward/actual-inverse outside frames,
including greatest continuation relations; Child/control synchronization remains open.
Definition 23 has a location-heap realization, distinct from host alias verification.
The six-field configuration entry is formalized independently of host parsing
and whole-tree reconciliation.

Version 0.1 has no stable API guarantee. Rust 1.98.1 and the exact `vstd` dependency
are intentional: verification also requires the pinned Verus binary and scripts
from the source distribution. `cargo test` alone does not check the proofs.

The proofs do not establish correctness of arbitrary external callbacks or the
entire asynchronous host runtime. Consult the source repository's
`docs/semantics.md` for contracts, assumptions, and the research provenance.
The source repository's `docs/paper-audit.md` records checked counterexamples to
paper v1 Lemmas 62, 75 and 77 and the unconditional closure clause of Theorem
71(2), using total Unit components. Child-based witnesses
for 78(2), 79 and 80 retain an unresolved original full-context component bridge;
they are not unconditional refutations of those original claims. General
confluence remains open. The audit states the precise alternative results.

Licensed under MIT; see `LICENSE` and `NOTICE` in this package.


The strict partial field refinement compares actual mixed-grammar run/restore
functions on a legal-input PER with equal controls. Table-only components admit
different root/current indices, histories and inverse-word lengths; all nine
target rules and complete finite traces are constructed. PER algebra and least
grammar self/alias witnesses are separate checked results. This does not identify
the controlled relation with the paper's full-context table-only observation.


The `paper_components`, `paper_observations` and `paper_confinement` APIs separate
the original conditional mathematical definitions from concrete interpreter
membership. Full-carrier witnessed components and generic function-field
observations are encoded; recursive context existence and strict-to-total
refinement are not inferred from these definitions.


`foreign_child_transport` proves real fresh Child landings and arbitrary-age
pure-Child retirement stacks across a deleted Table owner, including authentic
history compression and the live reference guard. It is a strict local bridge;
the original total-component interpretation remains a separate obligation.


`paper_typed_context` supplies all-input dependent-value projection gates and
actual FiberCodec recovery. `paper_instantiation` defines typed fresh insertion
with the full Component witness, name-dependent continuation, and strict captured
retirement under inhabited local editor laws. Neither constructs recursive Gamma
nor turns a missing-child inverse into identity.


`mixed_foreign_restore` and `foreign_child_deletion` compose arbitrary-age
foreign Table/Child journals, real captured retirement and dynamic Insert/Remove
with private Table-owner deletion. The surviving execution and final owner
recovery are derived; owner Child, owner consumers and general liveness remain open.


`paper_trace_independence` records the conditional full-history pairwise predicate,
recursive Child payload/root comparison and separate total/strict operation
adapters. Payload provenance is not the complete typed instantiation model;
the strict-to-total interpretation and original Lemma66 remain open.
