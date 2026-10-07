# Security policy

This is experimental research software. It has not received an independent
security audit, and the verified kernel is not a proof of the host runtime,
callbacks, configuration files, dependencies, or operating system. Plugins are
trusted native Rust code and are not sandboxed. Do not load untrusted plugin
code or treat formal verification as an isolation boundary.

Only the latest development revision and, once published, the latest 0.x release
are maintained. There is no guaranteed security response time or backport policy.

## Reporting

The repository is [validation-engineering/cordis-verus](https://github.com/validation-engineering/cordis-verus),
maintained by [Stool233](https://github.com/Stool233). GitHub private vulnerability
reporting is enabled. Use [Report a vulnerability](https://github.com/validation-engineering/cordis-verus/security/advisories/new)
to contact the maintainer privately. Do not post exploit details, credentials,
or user data in a public issue. Include the affected revision, platform, minimal reproduction,
impact, and whether the issue concerns a false proof claim or host behavior.

Ordinary non-sensitive correctness bugs and missing proof obligations can use
the issue templates. Dependencies are pinned in Cargo/toolchain locks and
reviewed through pull requests; CI does not replace ongoing advisory review.
