Describe the problem and resulting behavior. Link the issue or upstream reference.

Validation performed (paste exact commands and outcomes):

- [ ] `./scripts/check-development.sh` passes (whole proof, tests and packaging).
- Release quality (`./scripts/quality.sh`): state **passed / failed / not run** and attach evidence.
  Asset installation on every selected platform is also required for release.
- Independent full negative regression: state **passed / failed / not run**.
  It is not a normal release prerequisite; never imply unrun controls passed.
- [ ] Behavioral or proof regressions are covered where relevant.
- [ ] Public API or semantic changes are documented in `CHANGELOG.md` and the relevant guide.
- [ ] Proof claims and trusted assumptions still match the implementation.
- [ ] No secrets, downloaded upstream caches, or paper copies are included.

For kernel changes, identify contracts/invariants affected and any new hypotheses.
For dependency/toolchain changes, identify the immutable source and lock updates.
