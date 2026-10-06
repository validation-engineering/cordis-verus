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
initially private, maintained by [Stool233](https://github.com/Stool233).
Existing collaborators can request a private reporting route from the owner.
A monitored public vulnerability-reporting endpoint has not yet been configured.
Before making the project public, the maintainer must enable GitHub private
vulnerability reporting or publish a monitored private contact here.

If the published repository offers **Security → Report a vulnerability**, use
that private channel. Otherwise request a private reporting route from the
maintainer without posting exploit details, credentials, or user data in a
public issue. Include the affected revision, platform, minimal reproduction,
impact, and whether the issue concerns a false proof claim or host behavior.

Ordinary non-sensitive correctness bugs and missing proof obligations can use
the issue templates. Dependencies are pinned in Cargo/toolchain locks and
reviewed through pull requests; CI does not replace ongoing advisory review.
