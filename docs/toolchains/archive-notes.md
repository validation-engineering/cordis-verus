This archive preserves the original upstream Verus **0.2026.10.04.1687598** binaries used by Cordis Verus. It is a development dependency archive, not a Cordis runtime release or release-quality certification.

The upstream rolling release replaces its assets. These files were recovered from [official build 37171084467](https://github.com/verus-lang/verus/actions/runs/37171084467), commit `168759867f8c4ba0be848f5a3e438c75cee3e6e3`. Each inner ZIP must match the SHA-256 already committed in `toolchain.lock.json`; binaries are not rebuilt, repacked or patched. `provenance.json` records the recovery inputs and hashes.

`toolchain-sources.tar.gz` accompanies the binaries with the exact Verus source, locked vendored Cargo dependency sources and their notices, plus Z3's license. Those projects retain their own licenses; this is an independent archive, not an official Verus distribution. See the companion inventory for its scope and remaining platform/compiler attribution boundaries.

The archive tag is not a supported Cordis API version. Cordis package publication still requires the complete checks in `docs/releasing.md`. Do not replace these assets in place: a toolchain change requires a new reviewed lock and archive.
