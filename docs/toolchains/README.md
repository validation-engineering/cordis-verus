# Pinned toolchain archives

The Verus version, source commit and original ZIP SHA-256 values remain in
[`toolchain.lock.json`](../../toolchain.lock.json). Runtime users do not need
Verus; these tools are for contributors rebuilding proofs and release evidence.

## Install

```sh
./scripts/install-verus.sh
```

The installer reuses a verified local archive, otherwise tries the project's
GitHub release asset API, its download URL, and the original upstream URL. Every
transport must produce the same locked SHA-256 before the cache is replaced.
Failed downloads and extraction do not replace the working installation. A
failed automatic rollback reports the preserved backup directory.

While the repository is private, install GitHub CLI and authenticate with read
access to this repository (`gh auth login`). CI supplies a step-scoped `GH_TOKEN`
with `contents: read`; tokens are not passed on the command line or saved in the
lock. A public mirror can be fetched without authentication through its HTTPS
URL. Rustup is still required and the installer does not change its default.

## Why keep an archive

The original rolling release for `0.2026.10.04.1687598` returned HTTP 404 in all
three [development jobs](https://github.com/validation-engineering/cordis-verus/actions/runs/37627745933).
Upstream's rolling workflow replaces the assets of the same release. A pinned
tag alone therefore did not preserve a downloadable binary.

The [recovery manifest](verus-0.2026.10.04.1687598.json) identifies the successful
[official Actions run](https://github.com/verus-lang/verus/actions/runs/37171084467)
and each platform artifact. The recovery script checks the run's repository,
commit and success; checks each artifact's identity and expiry; and extracts only
the named original ZIP. The inner ZIP, not its Actions wrapper, must match the
hash already in the lock. No rebuild or repacking is substituted.

Upstream Actions artifacts expire. They are recovery inputs, not the long-term
installation location. The maintainer workflow preserves validated bytes under
`toolchain-verus-0.2026.10.04.1687598` in this repository's Releases. Release asset
IDs and download URLs are recorded in the lock after upload. The archive is
project-managed storage, not a guarantee that GitHub or maintainers can never
remove it; retain another verified copy when operating an independent mirror.

## Recover or update

Run the manual **Preserve pinned Verus toolchain** workflow, or stage recovery
locally:

```sh
python3 scripts/archive-verus-toolchain.py --output target/toolchain-archive
```

The script only reads GitHub and stages local files. The workflow additionally
bundles the exact Verus source, locked vendored Cargo sources/notices and Z3's
license, then uploads dependency assets. Its permission to write Releases is
limited to that manual job; development and full-quality jobs remain read-only.
The source companion records its inventory boundary and is not a complete
platform/compiler SBOM or an independent license audit.

Keep `provenance.json` and `toolchain-sources.tar.gz` with the original ZIPs.
Do not overwrite an existing archive tag or replace a hash to accept different
bytes. A future toolchain change needs a deliberate lock update, retained source
and attribution, proof/negative-control recalibration, and fresh platform checks.
The recovery script's failure paths have offline tests in
[`test_archive_verus_toolchain.py`](../../scripts/tests/test_archive_verus_toolchain.py).

This archive is a build dependency, not a Cordis runtime release. Restoring a
download does not establish release readiness; the full gate in
[releasing](../releasing.md), including canonical negative controls, still applies.
