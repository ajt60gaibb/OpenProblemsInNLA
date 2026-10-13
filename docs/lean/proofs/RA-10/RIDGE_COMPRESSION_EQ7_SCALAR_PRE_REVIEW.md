# RA-10 source Lemma 2, Equation (7): scalar coefficient-two gate

**Status:** source-only exact signature and numerical contract for independent pre-implementation review. No Lean implementation of this new public theorem may begin until that review approves these bytes. This gate is a single scalar step of Lemma 2, not the single-positive-eigenvector bound or the full positive-part inequality.

## Source locks

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `docs/lean/proofs/RA-10/RIDGE_COMPRESSION_POSITIVE_PART_PRE_REVIEW.md` | `ecbb548c34f50c6804e48c92ae6ff655ce99313f04858291dd83ca2d0cfe5d14` |
| `docs/lean/proofs/RA-10/RIDGE_COMPRESSION_POSITIVE_PART_INDEPENDENT_PRE_REVIEW.md` | `5685fa2ac7172d312ebf6f5ffbb7da0371e9143ca82f596a4be397fe1d7e2479` |

## Exact scalar source obligation

In source Lemma 2, a positive eigenvalue `λ` of `Z=f_s(C)−f_s(A)` satisfies `0<λ<1`; set `μ=λ/(1+λ)`, so `0<μ<1/2`. The second inequality in source Equation (7), after cancelling the identical deficit term from both sides, is exactly

```text
λ(s+c)/2 ≤ μs + μ(2−μ)c/[2(1−μ)].
```

The difference, right minus left, is exactly

```text
μ[s(1−2μ)+c(1−μ)]/[2(1−μ)] ≥ 0.
```

Both `s>0` and `c>0` are retained from source Lemma 2. In the selected-projector application, `c=a_k>0`, with one-based `k`; this scalar theorem does not replace that `c` or add a different cutoff. This statement keeps the coefficient `1/2` required for the full coefficient-two bound. Its algebra alone does not establish source Equation (5), Equation (6), the first inequality in Equation (7), or any matrix trace claim.

## Sole proposed public Lean theorem

Create a new, unimported `NLA.Proofs.RA10.RidgeCompressionEq7Scalar` module with exactly this public theorem:

```lean
namespace NLA.Proofs.RA10

theorem ridgeCompression_eq7_scalar
    {s c lam : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hlam : 0 < lam) (hlam1 : lam < 1) :
    let μ := lam / (1 + lam)
    lam * (s + c) / 2 ≤
      μ * s + (μ * (2 - μ) * c) / (2 * (1 - μ)) := by
  ...

end NLA.Proofs.RA10
```

The Lean binder `lam` denotes the source's `λ`; bare `λ` is reserved Lean syntax for a lambda expression. This binder spelling has no mathematical effect.

The module may contain private helper facts for the displayed exact difference. It must have no additional public theorem and no `sorry`, new axiom, native decision procedure, weakened numerical constant, or altered domain. After implementation, require pinned LeanCert `kernel` checking and printed axiom inspection. Leave the new source unimported and uncommitted for separate final audit.

## Numerical and boundary checks

- With `s=c=1` and `λ=1/2`, `μ=1/3`. The left side is `1/2`, the right side is `3/4`, and their difference is `1/4` by the displayed exact formula.
- With `s=2`, `c=3`, and `λ=1/3`, `μ=1/4`. The left side is `5/6`, the right side is `11/8`, and their difference is `13/24`.
- The limits `λ↓0` and `λ↑1` respect the source open interval; at `λ↓0`, both sides tend to zero, and at `λ↑1` the difference tends to `c/4`. These limits are checks, not substituted endpoint hypotheses.

Review must compare the exact Lean expression with the source's second Equation (7) inequality and confirm the computed differences before implementation.
