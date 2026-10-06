# Evidence you can inspect and reproduce

cordis-verus is a Validation Engineering project: we connect a software claim to
its specification, executable implementation, checks and remaining assumptions.
The practical question here is whether a plugin can finish cleanup while the
services it already depends on are being replaced or shut down.

Start with a case, then follow the contract. A passing test, a proved kernel
contract and successful application integration establish different things.

## Three entry points

| Question | Start here | Evidence type |
| --- | --- | --- |
| Can a consumer still write its final log during asynchronous cleanup? | [Lifecycle cleanup case](cases/lifecycle-cleanup.md) | The same plugin fixture executed on two pinned upstreams and two native profiles |
| Which paper clause constrains the running code? | [Paper review guide](paper-review-guide.md) | Five paper locations, contracts, executable calls and named regressions |
| Can this host run a useful existing application? | [cordis-harness](https://github.com/validation-engineering/cordis-harness) | Official Web/standard and headless compositions with original plugins, storage and AgentLoop |

The [comparison](comparison.md) explains capabilities, behavioral differences and
costs. The [evidence archive](evidence/README.md) retains differential results,
including failures. This is an experimental implementation; neither repository
is a published crate or npm release. Both repositories currently require access.

## Run the lifecycle case

Follow the [case's preparation and reproduction commands](cases/lifecycle-cleanup.md),
including the pinned upstream checkouts and the Rust/Node setup.
The runner preserves the input hashes, runtime versions and raw traces used to
evaluate its claims. It does not treat an expected difference as full API
conformance or establish what a different upstream revision will do.

The second case covers cleanup failure. Native disposal reports an error and
retains the failed inverse for an explicit retry. Separate
[disposal-failure regressions](../tests/node-compat/disposal-failure.test.mjs) check
provider retention during failed consumer cleanup. Upstream's pinned test
suite expects disposal to fulfill after a thrown inverse. This is a deliberate
contract difference, not evidence of a new upstream defect.

## Review the specification-to-code connection

The [five review cases](paper-review-cases.json) select committed provider
identity, retained child identity, the Lemma 62 counterexample, restricted
confluence and configuration projection. Each distinguishes the original claim,
its encoded model, any strengthened assumptions and the ordinary host boundary.
They supplement the [81-item paper ledger](paper-obligations.json); they do not
upgrade its statuses or complete the four outstanding integration obligations.

```sh
python3 scripts/check-paper-review.py
python3 scripts/record-development.py --offline
python3 scripts/record-development.py --check
```

The first command checks documentation references and known ledger statuses. The
second executes the development workflow, including whole-kernel Verus proof,
Rust/Node tests and packaging checks. The third only checks recorded evidence
against the local inputs and artifacts. A freshness check is not a new proof run.
The [development report](development-report.json) is the source of result counts.

The Node facade, ordinary Rust hosts, asynchronous callbacks, FFI and external
I/O have separate behavioral evidence. A proof about an abstract inverse cannot
make an arbitrary plugin callback reversible. The [architecture](architecture.md)
and [validation guide](validation.md) describe these trust boundaries.

## Reproduce the application

Use the companion [build guide](https://github.com/validation-engineering/cordis-harness/blob/main/docs/build.md)
and its [official validation record](https://github.com/validation-engineering/cordis-harness/blob/main/docs/official-validation-report.json).
Acceptance executes the real official AgentLoop and tool path; a local scripted
provider replaces only model responses. It covers the fixed official composition
and our extension fixtures, not every third-party plugin. Browser-side Cordis
remains upstream JavaScript. Interactive model use needs the user's configuration.

## What a useful independent review contributes

A review is most useful when it records the commit, command, toolchain and actual
output, then explains which claim it supports or contradicts. A minimal plugin
that violates a stated contract is more actionable than a general compatibility
claim. Use the repository's issue templates and [contribution guide](../CONTRIBUTING.md).
Do not include credentials, private prompts or proprietary plugin source.

The next review and release deliverables are:

- An independent reproduction of the cleanup case and the five paper review
  paths, including one reviewer-made change that is detected by the relevant check.
- Target-specific build and application evidence for each platform advertised;
  the recorded local development environment currently establishes macOS ARM64.
- The complete release gate, including full-crate negative controls, before a
  release acceptance claim. An experimental public source checkpoint can state
  its unfinished gates; a private vulnerability-reporting channel must be ready
  before changing visibility.
- A short application walkthrough using the official UI: tool execution, session
  recovery, configuration changes, failed cleanup and a Rust plugin replacement.

These are remaining deliverables, not completed adoption claims. Public visibility
and registry publication are separate decisions. We do not claim paper-wide
refinement, production readiness, independent external validation or general
performance superiority.

For project operations, track completed external reproductions, real plugin
integrations, reviewed contract corrections and contributions that keep their
checks reproducible. No external adoption count is asserted by this repository.
