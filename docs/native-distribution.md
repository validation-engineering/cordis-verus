# Native artifact distribution

The Node facade uses the same manifest selector in a source checkout and an
extracted npm installation. This is local packaging infrastructure. Packages remain
private; no registry publication, signing or complete platform acceptance is claimed.

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
