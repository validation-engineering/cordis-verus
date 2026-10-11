# Native artifact distribution

English | [简体中文](native-distribution.zh-CN.md)

The Node facade uses the same manifest selector in a source checkout and an extracted npm installation. GitHub Releases distribute three precompiled npm tarballs together with their proof, runtime and source provenance. These packages are not yet published to the npm registry.

## Install a published runtime without compiling

Install **Node.js 22.22+ with npm**, then run:

```sh
curl -fLO https://github.com/validation-engineering/cordis-verus/releases/download/v0.1.0-preview.1/install-cordis.mjs
node install-cordis.mjs --release v0.1.0-preview.1 --project my-cordis-app
cd my-cordis-app
npm start
```

On Windows PowerShell use `curl.exe` instead of `curl`. Rust, Verus, GitHub CLI, a source checkout and a C/C++ compiler are not needed. The installer downloads from the public release over HTTPS. For a private mirror, download assets with an authenticated client and use `--from-directory` below.

The installer selects the current macOS ARM64/x64, Linux x64 GNU or Windows x64 target,
downloads three existing npm tarballs plus their evidence, verifies size/SHA-256,
and installs with `npm --offline --ignore-scripts`. It verifies the installed native
manifest/provenance and actually loads both Cordis profiles before creating the
requested directory. An existing project is never overwritten. Download, hash,
package-installation and native-load failures remove staging directories and leave
the destination absent. Its parent directory must already exist.

The resulting project contains a working `app.mjs`, a package lock, retained
`.vendor/cordis/` tarballs for offline `npm ci`, and `cordis-release.json` recording
the source commit, target and manifest hash. Use normal imports from
`@cordis-verus/compat-cordis`, or start existing Cordis plugins with
`node --import @cordis-verus/compat-cordis/register app.mjs`. The loader and Harness
profile packages are installed alongside the same native lifecycle driver.

This delivers the **Node compatibility runtime**, not the complete Harness
application or custom Rust plugins. Pure Rust applications still consume Rust
crates; their application code must be compiled. Node remains an optional adapter
for existing JavaScript/TypeScript plugins.

For an offline machine, download the selected platform's `cordis-runtime-*.json`,
its referenced three `.tgz` assets and evidence JSON, plus `install-cordis.mjs`.
Use the same installer and verification path locally:

```sh
node ./release-assets/install-cordis.mjs \
  --from-directory ./release-assets --project ./my-cordis-app
```

Only install assets from a publisher you trust: package JavaScript and the native
addon execute during the smoke check. Hashes detect changed bytes, not publisher
identity. GitHub access and release review remain the trust boundary; signing and
attestation verification are not implemented. No network fallback or source build
is attempted when a target, dependency or binary cannot be used.

## Declared targets and evidence

| Target ID | Operating system / architecture | Required native interface |
| --- | --- | --- |
| `darwin-arm64-napi8` | macOS / ARM64 | Node-API 8 |
| `darwin-x64-napi8` | macOS / x64 | Node-API 8 |
| `linux-x64-gnu-napi8` | Linux / x64 / GNU libc | Node-API 8 |
| `win32-x64-napi8` | Windows / x64 / MSVC | Node-API 8 |

Every runtime release requires all four targets. The release runners are Ubuntu 24.04, macOS 15 (Apple Silicon and Intel), and Windows Server 2025 x64, using Node 22.22.0. Node-API 8 does not certify older Node versions. Older OS releases, lower glibc versions, Windows ARM64, Linux ARM64 and musl are not qualified by this matrix. Node 24 needs its own qualification despite satisfying the package engine range.

Each actual artifact records the host OS release, Node version, Node-API and module
ABI used when loading it. The build profile is recorded; a development build is not
silently relabeled an optimized release build.

## Build, select and verify

```sh
node scripts/build-node.mjs --offline
node scripts/check-npm-package.mjs
```

The first command obtains Cargo's actual output path, checks the ordinary core
addon and the separately built Rust SDK fixture, then writes:

- `packages/compat-cordis/native/cordis.node`
- `packages/compat-cordis/native/manifest.json`
- `packages/compat-cordis/native/provenance/<target>.json`
- `target/node-compat/build.json`

The manifest binds target and Node-API policy to binary size/hash and provenance
hash. Provenance binds the package/profile/driver ABI, source-file hashes, Cargo
and toolchain locks, build report hash, build profile and actual host load result.
A fresh Node subprocess loads a private byte snapshot; an existing `require` cache
cannot certify a replaced file. It rejects registered SDK factories for the default
core distribution. Generated native metadata is excluded from whole-source proof
fingerprints, but is included in npm distribution fingerprints.

```js
import { selectNativeArtifact, verifyNativeManifest } from '@cordis-verus/compat-cordis/native-artifacts'
const selected = selectNativeArtifact()
console.log(selected.path, selected.entry.target, selected.manifestSha256)
const inventory = verifyNativeManifest() // hashes every listed artifact; executes none
```

The selector checks platform, architecture, GNU/musl libc and Node-API before using
the artifact. Invalid manifests, changed binary/provenance bytes, duplicate targets,
unsafe paths and symlinks fail explicitly. The driver additionally validates its
runtime ABI/profile handshake. There is no automatic download or JavaScript
scheduler fallback. An absent target is an error, not cross-platform emulation.

`new Context({ addon: '/explicit/custom.node' })` and `CORDIS_NATIVE_BINDING` remain
explicit custom-addon paths with the existing runtime handshake. They do not acquire
default-manifest certification. The SDK fixture stays under `target/node-compat/`;
custom Rust factories must be shipped and audited separately. Package checks require
that every packed `.node` file is listed by the default-core manifest exactly once.

## Assemble locally supplied artifacts

```sh
node scripts/package-native.mjs --output /tmp/cordis-native-bundle /path/to/first/native /path/to/second/native
```

Use only artifacts whose build inputs match the intended source revision. Every
input manifest and byte hash is checked. Duplicate targets, mixed source snapshots,
existing outputs and overlap with input directories are rejected. The new directory
contains `manifest.json`, `provenance/` and `prebuilds/<target>/cordis.node`.
Aggregation preserves input provenance; it neither runs foreign binaries nor creates
new platform test evidence. It performs no downloads, uploads or registry actions.

The development and release-validation workflows assemble each successful job's
local native directory and retain `target/release-artifacts/native/` alongside its
build report and npm package report. Downloading such job artifacts and passing them
to this command is an explicit later step. Merely adding these workflow steps is not
evidence that any remote job ran or passed.

In a fresh packaging checkout at that same source snapshot, put the assembled
contents in `packages/compat-cordis/native/` and retain the current host's matching
`target/node-compat/build.json`. Then run `scripts/check-npm-package.mjs`. Its selector
works with both the original flat binary and assembled prebuild paths. Keep this
packaging directory free of leftover binaries; an unlisted binary fails the gate.
Rebuilding in that directory creates a new host-only manifest.

## Independent installation and limits

The offline package gate stages and packs all three packages, installs their tarballs
into an independent temporary project, and loads the selected native artifact. It
checks ESM/CommonJS identity, original Cordis imports, JSON Loader updates, Worker
loading and the Harness profile. It removes source-path/preload/custom-addon
environment overrides and confirms extraction rather than workspace symlinks.
The installed manifest must equal the checkout manifest. Reports include the actual
host target, manifest hash, source/build hashes and all three tarball hashes.

Development `--check` only rereads and hashes evidence; it does not execute Node,
npm or proofs. It needs the local native files, SDK fixture, build/package reports and
tarballs to remain present. A committed development report alone is insufficient.

SHA-256 provides byte-integrity and source binding, not publisher authentication.
Provenance remains an unsigned claim by its producing build environment; verifying
it does not prove an arbitrary supplied native program safe. Signing/attestations,
additional minimum OS/libc qualification remain separate work. JavaScript and native FFI behavior are not covered
by the lifecycle kernel's Verus proofs.

## Release asset production

[`package-runtime-release.py`](../scripts/package-runtime-release.py) reuses the
existing three independently installed tarballs and native provenance. It accepts
only a fresh `verification/v4` release record, checks complete positive proof and runtime evidence,
binds all package/build inputs, and requires a clean source commit (the newly generated
verification report is the only permitted tracked difference). It preserves the
actual native build profile rather than silently calling a development build optimized.

The [release workflow](../.github/workflows/release-validation.yml) runs the full quality gate, including the complete pinned Verus proof and compilation, on Linux. The other three platforms run [host acceptance](../.github/workflows/runtime-platforms.yml): Rust tests, examples, native/Node compatibility tests and independent extracted package checks. `record-runtime.py` explicitly records `proofExecuted: false` and cannot authorize a release alone.

The shared-proof policy currently permits only test and Verus ghost conditional compilation in the kernel. Release assembly rejects explicit platform/feature branches or generated kernel inclusions until their proof portability has been reviewed. All four declared runtime targets are 64-bit.

The collector requires identical source hashes and one commit across the full proof and every host record. `runtime-release/v3` keeps these records separate; a Linux runtime pass cannot stand in for a Windows or macOS pass. It checks native provenance and tarball hashes before staging. All four hosts then install the exact collected assets in a new directory containing spaces, run the example, and repeat it after offline `npm ci`. This installation job has no source checkout or compiler step.

[Whole-crate negative controls](full-negative-validation.md) remain independent and explicitly `not_run` in these release records. Proof contracts and scope are unchanged: platform tests do not prove Node, FFI or arbitrary plugins.

Dispatch with `create_draft=true` and a new `release_tag` to create a **draft prerelease** only after every required job succeeds. The draft contains all four asset sets, the standalone installer and `SHA256SUMS`. Existing tags are refused. Review and publish the draft after checking its results; the workflow does not publish automatically. See the [release procedure](releasing.md).
