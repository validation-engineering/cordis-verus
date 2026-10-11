# Working on cordis-verus

- `crates/cordis-kernel/src/` is executable Verus Rust, also compiled by Cargo.
  Do not introduce `assume`, `admit`, `external_body`, or unchecked replacement
  implementations to make verification pass. Use the pinned toolchain.
- Run `./scripts/check-development.sh --offline` for a development change with cached
  dependencies. It checks formatting/lints/docs, whole-kernel proofs, tests,
  examples and extracted crate builds. Use `scripts/record-development.py` to
  record this evidence; it does not claim release readiness. The release recorder
  also runs these shared checks and can record a release-quality change.
- A release requires `./scripts/quality.sh --offline`, with complete positive
  proof, runtime tests and packaging checks, followed by actual asset installation
  on every selected release platform. Full negative controls run independently
  through `negative-regression.yml` or `scripts/check-negative.py`; they are not
  prerequisites for a normal release. Preserve their strict rejection criteria.
  Release evidence must label them `not_run`, never passed or silently omitted.
  Do not label development/scoped checks as release or paper-wide acceptance.
- Refresh evidence with `python3 scripts/record-verification.py --offline`.
  Its `--check` mode detects stale records; it is not a new verification run.
- `crates/cordis/src/` is the ordinary Rust host adapter. Tests do not constitute
  a proof of arbitrary callbacks, asynchronous execution, or event dispatch.
- Preserve the distinction between current target and episode-committed provider
  identities. Active-target mismatch is a legal transient. Retirement is not
  registry removal, and ownership is not an implicit service dependency.
- Official research inputs are immutable snapshots in `upstream.lock.json`.
  The upstream checkouts, tool binaries, and full paper are local ignored caches.
  Changing the lock is an intentional update, never a side effect of testing.
- Keep claims in README and `docs/semantics.md` aligned with actual contracts.
  Do not claim complete Cordis/Harness compatibility or paper-wide proofs.
