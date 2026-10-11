# Runtime packages and the Harness application

[简体中文](package-boundaries.zh-CN.md)

`cordis-verus` implements Cordis. The companion Harness application runs the
official DeepSeek Harness composition on that runtime. These are separate
projects with separate upstream targets and acceptance checks.

| Package | Responsibility | Maintained by |
| --- | --- | --- |
| `@validation-engineering/cordis` | Shared Rust-backed Node runtime and ordinary Cordis interface | cordis-verus |
| `@validation-engineering/cordis-compat-deepseek` | Compatibility with `@deepseek-ai/cordis`, including its lifecycle interface and import routing | cordis-verus |
| `@validation-engineering/cordis-loader` | JSON Loader, domain transactions, Worker/process domains and Rust module loading | cordis-verus |
| `@validation-engineering/harness-verus` | Official CLI/Web/headless composition and version-specific Loader, ConfigEditor and HMR integration | Companion Harness application |

The DeepSeek compatibility package is an optional runtime interface. It does not
contain the agent loop, model providers, tools, session storage or Web UI. Its
types and policy regressions are maintained alongside the shared runtime. The
internal policy identifier remains `harness`; renaming a package does not change
the native protocol or lifecycle contracts.

The application owns interception of official application classes, Include write
barriers, module-cache replacement and recovery, and the corresponding real
official-workflow and type tests. These adapters use the runtime's domain
admission and cleanup APIs. The core runtime does not depend on the application.

## Migration from the initial npm release

Replace `@validation-engineering/cordis-harness` imports with
`@validation-engineering/cordis-compat-deepseek`, including the `/register` preload.
The original `cordis-harness@0.1.0` publication remains a compatibility library;
its name is not reassigned to the complete application.

Starting with `cordis-loader@0.2.0`, the application-specific `/harness` entry is
removed. Import `LoaderTransactions`, `installOfficialTransactions` and
`officialTransaction` from the companion application's `/official-loader-api`.
The application owns their implementation, declarations and acceptance tests.
Use the application release that advertises this export; an old application
snapshot cannot consume the new Loader automatically.

This describes the source layout and migration, not a claim that every named
version has already been published. Current availability is recorded separately
in the release notes. Previously published archives and historical evidence are
not rewritten by this refactoring.

## Verification boundary

Verus proves the executable kernel's specified contracts. JavaScript compatibility
policies, class adapters, Node module caches, application callbacks and external
I/O have behavioral tests, not a blanket Verus proof. Keeping a package in this
repository does not extend the kernel's proof boundary to that package.
