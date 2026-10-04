# Current status — 2026-10-04

This is an experimental development checkpoint for the initially private
[Stool233/cordis-verus](https://github.com/Stool233/cordis-verus) repository.
It is not a published crate, a production-readiness claim, or a completed
refinement of the entire paper.

## Verified checkpoint

The [development report](development-report.json) records the current whole-kernel
verification count and workspace test counts, bound to their exact source hashes.
The workflow uses `--no-cheating --compile` on the official Verus rolling release
`0.2026.10.04.1687598` and Rust `1.98.1`, and checks formatting and Clippy.
These are verification obligations and tests, not a count of paper theorems.
The behavior tests include 8,232 bounded lifecycle traces.

The source-bound [development report](development-report.json) records the fresh
checks for the prepared repository, including isolated package tests and builds.
Its schema differs from the [full release report](verification-report.json).
`python3 scripts/record-development.py --check` checks freshness, not new proofs.
Raw development logs and crate artifacts stay in `target/`.

The toolchain was checked against official release metadata on 2026-10-04.
This rolling release is pinned to `168759867f8c4ba0be848f5a3e438c75cee3e6e3`,
including a matching source checkout and three platform archive checksums.
The observed main branch was ahead at `fc7d32e1d9917d31dda119e5742286b10c0ffcd6`;
the project uses the published binary identified above. Cordis main still matched
the locked `f8ea3cd50f1a5724e8e715995bcde131c9c12b2c` revision.

The maintenance changes represent driver transitions and root setup ownership
with enums, unregister cancelled effect-join waiters, and share polling and
loader bookkeeping helpers. Started setup/effect futures remain owned by the
runtime until landing, and inverses are collected before cancellation cleanup.
Host regression tests cover these behaviors; they are not new async proofs.

## Paper coverage

The machine-readable [ledger](paper-obligations.json) is the source of truth.
The generated [coverage table](paper-coverage.md) links each item to contracts.

| Status | Numbered items | Meaning |
| --- | ---: | --- |
| `formalized` | 42 | Definition encoded, sometimes under a supplied interpretation |
| `proved` | 17 | Claim proved within its recorded scope and contract |
| `partial` | 18 | Some cases or bridges remain open |
| `refuted` | 4 | An original claim has a mechanically checked counterexample |
| **Total** | **81** | Counts are not a paper-completion percentage |

Four integration obligations remain open: whole lifecycle, reconciliation of
original and corrected statements, executable simulation, and host behavior.
A conditional Component definition does not construct recursive Γ or establish
that every runtime callback implements it.

Original Lemmas 62, 75 and 77, and the unconditional completion clause of
Theorem 71, have counterexamples. Original Child-related 78/79/80 remain partial:
encoded-rule obstructions do not instantiate every original total-context and
Component premise. See the [paper audit](paper-audit.md).

## Latest proof additions

- Typed Component and instantiation interfaces preserve per-key fibers, actual
  fresh identity and the captured child's retirement inverse.
- Restricted deletion composes foreign Unit/Operation/Provision/Child landings,
  mixed Table/Child journals and dynamic Insert/Remove. It constructs surviving
  executions and terminal recovery. Owner Child, private-provision consumers
  and unrestricted schedules remain outside this theorem.
- Strict function-field refinement retains real `None`/`Some` domains and
  permits different continuation identities and receipt lengths on its legal
  comparison domain.
- Historical independence includes internal children, removed entries and
  reused names. The total interpretation/strict implementation bridge remains open.

## Validation still open

There are **114 canonical negative mutations**. A complete full-crate negative
run for this source has not passed. The earlier 1,927-obligation snapshot's
full quality run stopped on `mixed-removal-ignores-retention` after a timeout.
Partial contract diagnostics were not accepted as a passed result.

The opt-in scoped-negative checker and candidate selector manifest are
experimental. Unit tests and selected probes do not establish a completed
114-control calibration and do not replace the full release gate. The first
full candidate calibration accepted 11 controls, then rejected control 12
(`begin-reuses-episode-generation`) because its real assertion failure was
accompanied by an SMT resource-limit failure. The run is **failed**, not a
completed calibration; its partial results are not release evidence.
See [validation](validation.md) for commands and evidence boundaries.

The local environment is macOS ARM64. Hosted Linux/macOS results must be checked
on the repository's Actions page after the push; configuration alone is not
cross-platform evidence. No crates.io upload or public release is part of this
checkpoint. Unfinished proof experiments are excluded. Next work and acceptance
criteria are in the [roadmap](roadmap.md).
