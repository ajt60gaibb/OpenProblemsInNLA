# Local RA-10 harmonic-extremal verification

Date: 2026-10-11. Branch: `codex/ra10-spectral-transfer`.
Baseline: `50106db1b75a1019b708f495db747ab37bb8efbd`.

Command, from `lean-statements/`:

```bash
lake build NLA.Proofs.RA10.HansenSplit
```

Result: successful local macOS build, 3022 jobs. The four new modules are
`LoewnerAtomMonotonicity`, `OperatorMonotonePositiveCone`,
`HarmonicExtremePoints`, and `HansenSplit`. All 32 new theorems, including
the two private scalar lemmas, have explicit kernel-trust checks. The exported
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

- `harmonic-extreme-build.log`: full successful build output.
- `harmonic-extreme-source-sha256.txt`: hashes of all 87 RA-10 proof files,
  the frozen statement, the toolchain and both Lake configuration files.

Proved without additional analytic hypotheses: harmonic-atom admissibility,
extremality of the constant and linear atoms, open-half-line cone bounds and
normalization, and positivity/algebraic identities of the canonical split.

The general extreme-point classification is still conditional on
differentiability at one and matrix monotonicity of both canonical pieces.
Neither those analytic results nor the unconditional frozen `Target` is proved.
Dependencies and the frozen statement are unchanged. This is implementation
evidence, not independent review or isolated non-root Linux Comparator verification.
