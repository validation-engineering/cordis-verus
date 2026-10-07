# Release procedure

No Cordis runtime release has been published. [Toolchain archives](toolchains/README.md)
preserve development dependencies and do not certify this project for release. The workspace crate manifests intentionally set `publish = false`:
the repository starts private at
[validation-engineering/cordis-verus](https://github.com/validation-engineering/cordis-verus). Registry names
and a monitored security reporting route must be confirmed before a public release.
The initial GitHub source snapshot is a development checkpoint, not a release;
see [current status](status.md) and [validation gates](validation.md). In particular, the
local name `cordis` is not a claim to that crates.io namespace.

## Local artifact dry run

```sh
./scripts/install-verus.sh
./scripts/quality.sh
# With previously fetched registry dependencies:
python3 scripts/package-check.py --offline
```

The package check uses Cargo to assemble each `.crate` archive, extracts it into
a temporary directory, rejects unexpected files and escaping paths, verifies
metadata/notices, and runs all targets, doctests, and an optimized library build.
During assembly a local patch lets Cargo resolve the unpublished kernel version.
During **build and test** the patch points only to the **extracted kernel archive**,
never to the original source tree. The normalized manifest keeps the exact
versioned dependency without a local path. Cargo metadata checks that all
non-registry dependencies stay inside the extracted artifacts. A shared build
cache contains only compilation outputs.

`cargo package --no-verify` is used only for the assembly step; separate real
artifact builds/tests must succeed before the script reports success. This is
not a registry upload simulation: it cannot establish name ownership, registry
policy compliance, or that the kernel has been published. No command in the
quality scripts uploads a package or creates a remote repository.

Archives and their SHA-256/file manifests are under `target/release-artifacts/`.
The report is generated from the current files, not copied from a previous run.
CI retains each platform's logs and archives for 14 days. The package archives
contain license and attribution files; ignored toolchains, upstream checkouts,
paper copies, and build outputs must not appear in them.

## Maintainer checklist

1. Confirm ownership of the public repository and the required registry names; rename
   packages/imports if needed. Set real `repository`/`documentation` links and
   the private reporting route in `SECURITY.md`. Enable private vulnerability
   reporting before announcing a release. Review the selected MIT license and
   upstream attribution. Configure branch protection for all quality jobs.
2. Review known limitations, issue backlog, dependency advisories, and proof
   assumptions. Do not describe 0.1 as audited, production-proven, or a complete
   paper implementation. All three CI platforms must actually pass.
3. Choose matching crate versions and the exact host-to-kernel dependency.
   Update `CHANGELOG.md`, Rust/toolchain policy if changed, and migration notes.
   Refresh the checked verification report from the exact release sources with
   `python3 scripts/record-verification.py --offline` (add `--upstream` when inputs
   are cached). `--check` detects stale hashes but does not execute verification.
4. Run `./scripts/quality.sh` on the release revision. Review package contents
   and SHA-256 hashes. Confirm a clean working tree; local checks deliberately
   permit dirty packaging for development, which is not acceptable for release.
5. Only after explicit maintainer authorization, enable publication and perform
   a real `cargo publish --dry-run -p cordis-kernel`. Upload the kernel first,
   wait for registry availability, then dry-run the host with the published
   kernel before any host upload. A local patched artifact check cannot replace
   these registry checks. Publishing is a separate manual action.
6. Tag the reviewed commit, publish release notes with proof/behavior results
   and remaining assumptions, and attach the tested archives/checksums. Verify
   clean consumer builds from the registry and docs after publication.

Cargo's [package rules](https://doc.rust-lang.org/cargo/commands/cargo-package.html)
and [versioned path dependencies](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html#multiple-locations)
define the packaging behavior. CI pins external actions to immutable commits
and uses a read-only token, following GitHub's
[secure-use guidance](https://docs.github.com/en/actions/reference/security/secure-use).
