# Local RA-10 analytic-prerequisite verification

Date: 2026-10-11. Branch: `codex/ra10-spectral-transfer`.
Baseline: `50106db1b75a1019b708f495db747ab37bb8efbd`.

Command, from `lean-statements/`:

```bash
lake build NLA.Proofs.RA10.HansenSplit NLA.Proofs.RA10.OperatorMonotoneConcavity
```

Result: successful local macOS build, 3038 jobs. Five new modules contain
23 theorems, all with explicit kernel-trust checks: `SpectralFunctionalCalculus`,
`MatrixFunctionalCalculus`, `OperatorMonotoneCompression`,
`OperatorMonotoneConcavity`, and `OperatorMonotoneDifferentiability`.
The existing `HansenSplit` now uses the proved differentiability theorem;
its classification result no longer assumes differentiability.
Exported transitive axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`.

- `analytic-prerequisites-build.log`: full successful build output.
- `analytic-prerequisites-source-sha256.txt`: hashes of all 92 RA-10 proof
  files, the frozen statement, the toolchain and both Lake configuration files.

Proved: spectral-basis independence, functional-calculus bridges, positive-definite
block compression, all-size matrix concavity, and differentiability of every
compact-class profile at every positive argument. Continuity of both Hansen
pieces is now unconditional for members of that class.

Still open: all-size matrix monotonicity of the two Hansen divided-difference
pieces. Consequently the general harmonic classification, application of the
measure constructor to arbitrary admissible functions, and unconditional
`Target` remain open. The frozen statement and dependencies are unchanged.
This is local implementation evidence, not independent review or isolated
non-root Linux Comparator verification.
