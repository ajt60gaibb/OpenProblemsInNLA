# MI-31 independent Lean boundary review

Reviewer: OpenAI Codex AI agent `/root/infrastructure`, 2026-10-09. I did not author the MI-31 specification, live Lean source, shared exponent source, or frozen source. Phase: `lean-boundary`. Verdict: **APPROVE** for the exact statement boundary after the shared-exponent repair. This reviews the statement, not a proof of the Gaussian inequality or external human peer review.

## Exact `check.py` review inputs

| Input | SHA-256 |
| --- | --- |
| `matrix-inequalities-and-norms/MI-31/README.md` | `9d49717605baf2379896f6360417092c70bb74773120002cd5f4c15950a04093` |
| `docs/lean/statements/MI-31/ORIGINAL.md` | `9d49717605baf2379896f6360417092c70bb74773120002cd5f4c15950a04093` |
| `docs/lean/statements/MI-31/NUMERICAL_TARGETS.md` | `e1d5dc6fdb06b16cbcf95d2a648f435d4cdd8bcefd2a0e13034e0cfe93556b76` |
| `lean-statements/NLA/Statements/MI31.lean` | `f931dad64f75fd65b2b2f8006f15ecb657ec87f1a5d8542702cde26e94a6ba1d` |
| `lean-statements/Reviewed/MI31.lean` | `6f9570ca3c591c571222023c5137861c074c9db3a71d8cd31b6bad4a69bac0f1` |
| `lean-statements/NLA/Statements/Shared/MI31Exponent.lean` | `e49f3be423539f5ad9fa560ec268c8f67969ed9acf5767a3742628a80510d8f6` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

These are all paths returned by `tools/lean_statements/check.py` `review_inputs` for MI-31's `lean-boundary` phase, including the complete repository-local import closure and the toolchain/dependency pins. The canonical README and retained `ORIGINAL.md` are byte identical. The shared `MI31Exponent` module defines only a concrete finite-real-or-infinity inductive type, used by both boundaries; it introduces no answer oracle or hypothesis. The frozen module is exactly the live source after the namespace substitution and explicit opening of that shared exponent type, plus the standard frozen-source header.

## Mathematical and numerical meaning

I checked the revised definitions against the approved specification and complete canonical README. Finite vector norms are `(∑ |xᵢ|^r)^(1/r)` using exact real powers. At the infinity endpoint, the vector norm is the supremum of its finite coordinate set, a genuine maximum in all positive dimensions quantified by `Target`. `OperatorNorm` takes the supremum over **every** real input vector in the actual ℓ_p unit ball after the ordinary rectangular matrix-vector action. `ConjugateExponent` gives `p*=∞` at `p=1` and the exact `p/(p−1)` formula otherwise; `CappedExponent` gives `min(r,L)` for finite `r` and `L` at infinity. Thus both `p*=∞` and `q=∞` use the correct vector norms and logarithmic caps. `LogCap` is exactly `max(1,ln k)`.

Mathlib documents `gaussianReal μ v` with **variance** `v` and proves that variance identity, so `gaussianReal 0 1` gives standard real `N(0,1)` in each coordinate. The finite `Measure.pi` supplies independent coordinates. `WeightedGaussian` multiplies each draw by its corresponding real matrix entry. `RowScale` and `ColumnScale` maximize exactly the row ℓ_(p*) and column ℓ_q norms of that deterministic matrix. `EntryMaximum` is the samplewise maximum of the absolute weighted entries, and only this maximum is inside its expectation; the row and column terms are outside expectations. The left side integrates the actual induced norm of the same weighted Gaussian matrix.

The single positive real `C` precedes every positive pair of dimensions, every `1≤p≤2`, every finite `q≥2` or `q=∞`, and every real matrix profile. The displayed terms have the original square-root caps, plus signs, and weak upper inequality only. I found no weakened endpoint, restricted profile, missing quantifier, or changed numerical convention.

## Kernel and boundary checks

With the pinned Lean 4.33.1 toolchain, `lake build NLA.Statements.MI31 Reviewed.MI31` passed (3109 jobs). Both modules' `#assert_statement` and `#assert_trust kernel` passed. Their printed axiom closure is the standard `propext`, `Classical.choice`, and `Quot.sound`. In a fresh file importing both modules, the exact identity certificate

```lean
example : NLA.Statements.MI31.Target = NLA.ReviewedStatements.MI31.Target := by rfl
```

also passed. The earlier duplicated-type boundary failure is resolved by the common imported `ExtendedExponent`. No MI-31 Lean source was edited in this review.
