# One-Dimensional Quantum Scattering — F2 on Lean 4.35.0

**Local release verification passed.** The fixed source hashes and the 55
axiom audits are recorded in [the release verification record](docs/release-verification.json).
See [the repair report](FIX_REPORT.md) for the changes from the original candidate.

The formalization constructs classical stationary scattering waves for an
arbitrary finite list of real constant-potential layers with two open leads.
It proves existence and uniqueness for two-sided incidence, conservation of
probability current, and unitarity and reciprocity of the flux-normalized
scattering matrix. The single rectangular layer is checked against the
vendored rectangular-barrier model, including the complex amplitudes.

```bash
bash scripts/complete_lean435.sh
```

With the pinned dependencies already prepared in `.lake/packages`, rerun
offline with `bash scripts/verify.sh --target release`.

The fixed environment is `leanprover/lean4:v4.35.0` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The checked Lake resolution is
recorded in `lake-manifest.json`, and the expected commits are in
`toolchain-lock.json`.

The release endpoint is `QuantumScattering.reusable_scattering_framework_release`.
The default Lake target is `QuantumScatteringRelease`. The release verifier
also compiles the independent core and Q5 modules, all three example suites
and both generated bundles. It checks all 55 named audit declarations and
records the source hashes before and after verification.

## Scope and history

The pre-repair handoff is recorded in `MIGRATION_REPORT.md` and
`migration-baseline.json`. Mathematical scope is in `FRAMEWORK_SCOPE.md`.
