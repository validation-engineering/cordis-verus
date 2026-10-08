# Native artifact distribution

English | [简体中文](native-distribution.zh-CN.md)

The Node facade uses the same manifest selector in a source checkout and an
extracted npm installation. The three npm packages can be delivered as precompiled GitHub Release assets.
No runtime release has been published yet; the commands below become usable after
a maintainer publishes a validated runtime draft. The source repository is public;
its npm packages remain unpublished. Registry publication and signing are separate work.

## Install a published runtime without compiling

Prerequisites are Node.js 22.22+ with npm, and the [GitHub CLI](https://cli.github.com/manual/gh_release_download).
A private repository also requires `gh auth login` with read access. Rust, Verus,
a source checkout, and a C/C++ compiler are not needed. Choose an explicit published
runtime tag from the repository's Releases page; toolchain archive tags are not
runtime releases.

```sh
# Replace the placeholder with a published runtime tag. No runtime tag exists yet.
CORDIS_RELEASE_TAG='<published-runtime-tag>'
gh release download "$CORDIS_RELEASE_TAG" \
  --repo validation-engineering/cordis-verus \
  --pattern install-cordis.mjs --dir ./cordis-installer
node ./cordis-installer/install-cordis.mjs \
  --release "$CORDIS_RELEASE_TAG" --project ./my-cordis-app
cd my-cordis-app
npm start
```

The installer selects the current macOS ARM64/x64 or Linux x64 GNU target,
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

These are allowed artifact targets, not a passed test matrix. The package engine
requires Node 22.22 or newer; Node-API 8 does not certify older Node releases. Node 24,
Windows, Linux ARM64 and musl have not gained acceptance through this implementation.
OS deployment versions and minimum glibc compatibility need separate release tests.
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
minimum OS/libc release qualification and a passed multi-platform release matrix
remain separate acceptance work. JavaScript and native FFI behavior are not covered
by the lifecycle kernel's Verus proofs.

## Release asset production

[`package-runtime-release.py`](../scripts/package-runtime-release.py) reuses the
existing three independently installed tarballs and native provenance. It accepts
only a fresh full release record, checks the exact ordered negative-control manifest,
binds all package/build inputs, and requires a clean source commit (the newly generated
verification report is the only permitted tracked difference). It preserves the
actual native build profile rather than silently calling a development build optimized.

The [full release workflow](../.github/workflows/release-validation.yml) runs all
three platforms. Each first completes twelve strictly collected
[whole-crate negative shards](full-negative-validation.md), then the complete
quality/package gate. It installs each staged runtime in a new project and checks a second
offline `npm ci` followed by the example. When explicitly dispatched with
`create_draft=true` and a new `release_tag`, it collects all three matching-commit
asset sets, adds `SHA256SUMS`, and creates a **draft prerelease**. Any failed platform
prevents this job from running. It refuses an existing tag and never publishes the
draft automatically. A development workflow cannot upload runtime releases.

A workflow definition is not execution evidence. The first runtime release still
requires successful full-quality runs on its exact commit and maintainer review.
See [the release procedure](releasing.md) for the remaining release checklist.
