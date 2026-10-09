# MI-31 Lean statement boundary: independent review

**Verdict: APPROVE.** Reviewer: `/root/inventory_review`, 2026-10-09. This is an exact-statement review, not a proof of the Gaussian inequality or an endorsement of the cited candidate proof.

I compared the canonical README, its original problem TeX, the approved numerical specification, the live statement, the frozen statement, and their repository-local imports. The shared `Shared/MI31Exponent` module defines exactly the finite real and infinity constructors. Except for its freeze comment, namespace, and opening that shared type, the frozen statement is textually identical to the live statement.

`gaussianReal 0 1` is Mathlib's real Gaussian with mean zero and **variance** one; the finite `Measure.pi` supplies one independent coordinate for each pair `(i,j)`. `WeightedGaussian` multiplies each arbitrary real profile entry by that coordinate. `FiniteLpNorm` takes the real `r` power sum of absolute coordinates and its `1/r` power, while `InfinityNorm` takes the supremum of the finite absolute-coordinate set. `OperatorNorm` takes the supremum of the output norm over the entire real input `ℓ_p` unit ball. Thus no exponent rounding, Euclidean surrogate, or restricted vector family enters the target.

The target quantifies one positive constant before every positive pair of dimensions, every real `1≤p≤2`, every finite output exponent `q≥2` or the infinity endpoint, and every rectangular real matrix. `ConjugateExponent` implements `p*=∞` at `p=1` and `p/(p−1)` otherwise. `LogCap` is `max(1,ln k)`, and both capped exponents apply `min` at finite exponents and the cap itself at infinity. `RowScale` and `ColumnScale` are maxima of the actual deterministic row and column norms. `ExpectedOperatorNorm` integrates the induced norm; `ExpectedEntryMaximum` integrates the samplewise maximum absolute entry, so the expectation is placed inside the prescribed last term. The statement is exactly the uniform upper bound, including `p=1`, `q=∞`, and one-dimensional matrices.

Pinned local `lake build NLA.Statements.MI31 Reviewed.MI31` succeeded with Lean 4.33.1. LeanCert kernel assertions accepted both definitions. `#print axioms Target` reported only `propext`, `Classical.choice`, and `Quot.sound` in each namespace. This is local typechecking and statement-boundary verification, not the separate Linux Comparator run.

## SHA-256 review inputs

The first ten paths are precisely the `tools/lean_statements/check.py` `lean-boundary` review-input closure. I additionally inspected the original problem TeX.

| Path | SHA-256 |
| --- | --- |
| `docs/lean/statements/MI-31/NUMERICAL_TARGETS.md` | `e1d5dc6fdb06b16cbcf95d2a648f435d4cdd8bcefd2a0e13034e0cfe93556b76` |
| `docs/lean/statements/MI-31/ORIGINAL.md` | `9d49717605baf2379896f6360417092c70bb74773120002cd5f4c15950a04093` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/NLA/Statements/MI31.lean` | `f931dad64f75fd65b2b2f8006f15ecb657ec87f1a5d8542702cde26e94a6ba1d` |
| `lean-statements/NLA/Statements/Shared/MI31Exponent.lean` | `e49f3be423539f5ad9fa560ec268c8f67969ed9acf5767a3742628a80510d8f6` |
| `lean-statements/Reviewed/MI31.lean` | `6f9570ca3c591c571222023c5137861c074c9db3a71d8cd31b6bad4a69bac0f1` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `matrix-inequalities-and-norms/MI-31/README.md` | `9d49717605baf2379896f6360417092c70bb74773120002cd5f4c15950a04093` |
| `matrix-inequalities-and-norms/MI-31/problem.tex` | `acc3912af8aab04f508643f2ba14d029003dc3fc7349ead7a08d953ba0227a87` |
