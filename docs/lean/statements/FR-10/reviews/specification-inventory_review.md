# FR-10 independent specification review

**Verdict: APPROVE.** This approval concerns the mathematical and numerical specification, before any FR-10 Lean implementation. It is an independent AI-agent review, not a proof of the Walsh restricted-isometry theorem or a review of future Lean definitions.

## Inputs reviewed

Published base: `0e916df335209819b5bf9bb8ed8f65ea978c049d` (`origin/main`). SHA-256:

| Input | SHA-256 |
| --- | --- |
| `frames-and-matrix-designs/FR-10/README.md` | `6e7f8ddb900da1cef486a6196c3ac277e79c7d0c953099b0e27441efea569e44` |
| `docs/lean/statements/FR-10/ORIGINAL.md` | `6e7f8ddb900da1cef486a6196c3ac277e79c7d0c953099b0e27441efea569e44` |
| `docs/lean/statements/FR-10/NUMERICAL_TARGETS.md` | `4302bb580024b66b0bdc7e65e493eefdba2ae33659c7181757f5965aea85cad3` |
| `references/haidary-resolutions-2026-09-30/Walsh_RIP_with_replacement_revised.tex` | `634946e8576c0c7f41fda7e18e2e5f55e6aec9dbaaaf8aaffc2018ca7b84d22e` |

`ORIGINAL.md` is byte-for-byte identical to the canonical README (`cmp` succeeded).

## Mathematical comparison

The specification retains the complete original parameter range `d ≥ 1`, `N = 2^d`, `1 ≤ k ≤ N` and the resolved uniform all-sparsity conclusion. Indexing rows and columns by `G = (𝔽₂)^d` gives exactly `N` coordinates. Uniformly counting ordered functions `Fin m → G` is the source's independent sampling with replacement, including repeated rows and `m > N`.

The energy expression `(1/m) ∑ᵢ (∑ᵦ (-1)^(aᵢ·b) xᵦ)^2` is algebraically equal to the squared norm of `√(N/m)` times the normalized Walsh rows. This removes square roots from the statement without changing its value. The event requires one sample to satisfy both non-strict RIP inequalities, with coefficients `1/2` and `3/2`, for every **real** vector of support size at most `k`.

The probability is exact finite uniform counting, with inclusive success threshold `9/10`. The minimum is over **positive** sample counts; the specification explicitly requires nonemptiness and forbids silently treating `Nat.sInf ∅ = 0` as a valid minimum. It assumes no monotonicity in sample count.

The final formula has `mStar(d,1) = 1` and positive constants independent of both `d` and `k`, with natural logarithms and factors `k log(2k) log(2e·2^d/k)` on both sides for every `2 ≤ k ≤ 2^d`. The TeX source states the stronger lower coefficient `1/2000`; the specification correctly labels that coefficient as an optional additional resolution target while retaining the original existential-constant target. It includes `d = 1`, `k = N`, and the full with-replacement dense regime. The source's proof-side probabilities `23/24` and greater than `1/7` do not replace the original `9/10` threshold.

No substantive mismatch or missing original FR-10 target was found. The later Lean boundary still requires independent review of its actual definitions and imports against these frozen inputs.
