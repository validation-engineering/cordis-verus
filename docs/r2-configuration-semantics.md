# R2 package 3: configuration meaning in the running Loader

Current R2 status is defined by [package 5 acceptance](r2-acceptance.md): managed-production/v1 is complete. Earlier checkpoints below retain their original evidence and scope.

[Package 4](r2-production-composition.md) joins the actual typed configuration/source projections and native Insert origins; final R2 acceptance remains separate.

[简体中文](r2-configuration-semantics.zh-CN.md) · [Configuration protocol](r2-configuration-execution.md) · [Paper map](paper-refinement-map.md)

The native JSON Loader now executes configuration interpretation in the verified
kernel: it selects the registered module, applies inherited interception,
normalizes the complete configuration against that module's schema and retains
an immutable recipe for mounting, updates and recovery. Persistence uses checked
three-way merging and accepts a source projection only after a complete round
trip through the real include expander.

This closes the configuration-data and binding layer of the third R2 package.
**R2 remains in progress.** The fourth package must compose all production steps
and observations; the fifth provides the combined R2 acceptance. Arbitrary
module bodies do not acquire a Component proof by passing a configuration schema.

## Guarantees on the actual path

| Actual operation | Checked contract | Practical consequence |
| --- | --- | --- |
| `FactoryRegistry::register` / `Loader::prepare` | `Modules::prepare` selects the actual retained `Definition`, executes interception and its stored schema, and returns `Prepared::wf`. | A recipe cannot silently bind the raw config when interception or defaults changed it. Re-registration does not replace a saved factory reference. |
| Parent-to-child configuration scope | `Modules::extend` preserves all existing bindings except the supplied overrides; `data::apply` implements recursive object overlay. | Metadata and injection configuration inherit by key. Interception merges recursively; arrays, scalars and null replace rather than implicitly delete. Parent scopes retain their original values. |
| Schema validation | `Schema::validate` returns exactly `normalized`, or rejects when it is undefined. | All array elements and declared object fields are traversed. Defaults are themselves validated, required fields and unknown keys are checked, and numeric ranges are inclusive. |
| Mount, config update and recovery | The host decodes the same `Prepared::config` and invokes its retained module with its retained scope. Existing checked update and reconstruction owners retain the recipe. | Planning and execution do not independently re-resolve a mutable factory name. Schema compilation is cached at registration. |
| Three-way save | `MergeProof::valid` covers every key from base, local intent and observed disk content, recursively. | Disjoint edits survive, deletions are distinguished from null, incompatible changes reject the whole plan before writing. |
| Keyed child ordering | `ordered` requires every live member exactly once. | A chosen ordering cannot silently omit a newly merged entry or repeat an entry. Ordinary JSON arrays remain atomic values. |
| Projection back to include files | `RoundTrip::check` compares the complete requested tree with the actual expanded proposed documents. | Matching revisions or entry counts cannot hide a changed nested field, missing subtree or cross-file ordering change. Shared include instances must remain consistent. |

Save reports still distinguish replacement from directory durability. A failed
later file does not roll back earlier writes, and the existing checked source
owner advances only acknowledged local checkpoints. The new data contracts
compose with those protocols rather than replacing them with an atomic-file-set
claim. Only a subsequent reload applies merged external changes to running
plugins.

## Paper interpretation

Definition 81's six fields remain distinct: the parent-local ID, module,
isolation, interception, raw bound configuration and this entry's administrative
status. `Prepared::entry` interprets the resolved module and raw configuration;
`Prepared::wf` additionally connects that raw value to the actual effective
argument after interception and schema normalization. Registered names are
resolved through the real table, not treated as external URLs without a resolver.
The earlier `Entry::as_paper_entry` API remains a conservative resolved-leaf view.

The checked planner already establishes the complete preorder, effective enabled
status and parent-local ownership. The checked expander already attaches every
included forest below its requesting entry, in inline-then-include order, with
actual read provenance and cycle/depth checks. This package supplies the missing
value interpretation and source round-trip check around those real traversals.

The native Loader elaborates groups into a **verified empty service program**
plus the owned children managed by the existing structural insertion protocol.
It no longer installs an opaque no-op Rust callback for a group. Include files
are expanded before planning; they do not create a second hidden runtime tree.
This is the explicit lowering used by this Loader. It is not a claim that an
arbitrary JavaScript group/include plugin has the same verified callback body.
The final correspondence between the complete production sequence and paper
steps is documented in package 4; the original total Component/termination/confluence
claims and the R1 semantic revisions are unchanged.

## Review boundary

The trusted/audited adapters remain small and explicit:

- `config_data.rs` translates serde JSON values to checked structured values and
  back, preserving encoded scalar values and distinguishing null from an absent key.
  Incoming object keys use serde's canonical ordering; enum and merge equality
  compare object fields by key even after overlay adds keys. JSON floating signed zero compares
  equally for enum/merge decisions while selected values retain their sign;
  integer identity does not collapse through an `f64` conversion.
- The adapter classifies scalar types and maps floating comparison operands to
  ordered IEEE-754 keys. JSON parsing, that encoding, serialization and filesystem
  identity/I/O are not proved by the kernel. The checked interpreter performs
  range decisions, defaults and recursive validation itself. `Schema::compile`
  remains an audited one-to-one translation from the public schema constructors
  to the checked schema stored with the factory.
- Registration supplies actual Rust factory closures and service keys. Their
  external effects, factory-result declarations, arbitrary cleanup inverses,
  scheduler fairness and eventual return require their existing separate
  contracts. Node's arbitrary JavaScript values, module evaluation and custom
  schema callbacks are covered only by their stated host/dispatch boundaries.
- A successful source round trip concerns the reviewed structured snapshot.
  Existing rechecks protect the subsequent save; this is not a filesystem CAS,
  a cross-file transaction, or a proof of eventual convergence.

These are interpretation/foreign-system boundaries, not unimplemented merge or
schema loops hidden behind assumptions. No `assume`, `admit`, `external_body` or
unchecked replacement was added to make the proofs pass.

## Evidence and reproduction

Review the actual producers in
[`configuration_module.rs`](../crates/cordis-kernel/src/configuration_module.rs),
[`configuration_binding.rs`](../crates/cordis-kernel/src/configuration_binding.rs),
[`configuration_schema.rs`](../crates/cordis-kernel/src/configuration_schema.rs)
and [`configuration_data.rs`](../crates/cordis-kernel/src/configuration_data.rs).
The production callers are `loader.rs`, `config.rs`, `config_data.rs` and
`persistence.rs` in the `cordis` host crate.

The [development record](development-report.json) binds the complete positive
proof, Rust/Node regressions and package checks to the current source. Check its
freshness with `python3 scripts/record-development.py --check`. Reproduce the
complete acceptance with `python3 scripts/record-development.py --offline`.

Focused cases cover retained factory references, interception and defaults,
conflicting updates/deletions, complete source equality, exact child coverage,
floating zero and large integers, literal diagnostic field names, existing
include topology checks, cancellation/recovery and partial-save retry. Four
canonical mutations deliberately accept a changed round trip, drop a disk edit,
skip a default or ignore interception. Selected rejection evidence requires a
matching positive, compilable mutant and the named contract failure. It is not
full negative regression, release acceptance or whole-paper acceptance.
