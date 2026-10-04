Describe the problem and resulting behavior. Link the issue or upstream reference.

Validation performed (paste exact commands and outcomes):

- [ ] `./scripts/check-development.sh` passes (whole proof, tests and packaging).
- Full release gate (`./scripts/quality.sh`): state **passed / failed / not run** and attach evidence.
  Development checks alone do not imply release acceptance.
- [ ] Behavioral or proof regressions are covered where relevant.
- [ ] Public API or semantic changes are documented in `CHANGELOG.md` and the relevant guide.
- [ ] Proof claims and trusted assumptions still match the implementation.
- [ ] No secrets, downloaded upstream caches, or paper copies are included.

For kernel changes, identify contracts/invariants affected and any new hypotheses.
For dependency/toolchain changes, identify the immutable source and lock updates.
