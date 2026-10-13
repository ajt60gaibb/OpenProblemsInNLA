# SP-14: bounded finite-support inverse map before L² extension

**Status:** source-only exact mathematical/indexing contract for independent review. No Lean source for this map has been written.

## Locks and scope

The frozen `lean-statements/NLA/Statements/SP14.lean` SHA-256 is `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`; canonical `counterexample.tex` at `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/` SHA-256 is `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`. The approved completed-inverse goal is `ENDPOINT_INVERSE_PARSEVAL_COMPLETION_PRE_REVIEW.md` SHA-256 `cd170cdb4d4fd1070edfc9185a0475432e8a3db9e83a9d794cb58b08ce6dd4e9`.

Exact finite inputs and bounds: `EndpointFiniteInverseParseval.lean` SHA `923d5323e98301c91c0ad8f57619bc1475ce685b78785e096a495f3cdf0bb0b5`, `EndpointFiniteInverseNorm.lean` SHA `7b2678fd53cededb71dd8e016b75cc56d2c76fbce1ff387a7ebdedb97ed6ec34`, `EndpointFiniteInverseTruncation.lean` SHA `b362fe688ccb49f24bbecb227daccbc90d8eaaae8552b8579732414d515509b6`, `EndpointFiniteInverseLinearity.lean` SHA `c9c48b126d81a773a323f62ee59d643e6bce8083ae4a98a15146c135223a0454`. The independently pre-reviewed and directly kernel-checked dense carrier is `EndpointInverseL2Dense.lean` SHA `f772c3b09528367fcceeb16f606043a4ac279d7ba6928f6f99190428ba424e0a`.

## Proposed public signatures

Let `μ := AddCircle.haarAddCircle (T := 2 * Real.pi)` and `D_r := endpointFiniteSupport r` with its exact weighted-coordinate support carrier. The candidate implementation may choose a support bound for each `y : D_r`, but the map must be independent of that choice.

```lean
noncomputable def endpointFiniteSupportInverse (r : ℝ) :
    endpointFiniteSupport r →ₗ[ℂ]
      MeasureTheory.Lp ℂ 2 (AddCircle.haarAddCircle (T := 2 * Real.pi))

noncomputable def endpointFiniteSupportTruncation (r : ℝ)
    (N : ℕ) (y : SobolevCoeff r) : endpointFiniteSupport r

theorem endpointFiniteSupportInverse_eq_finite (r : ℝ)
    (y : endpointFiniteSupport r) (N : ℕ)
    (hN : ∀ n : ℕ, N ≤ n → (y : SobolevCoeff r) n = 0) :
    endpointFiniteSupportInverse r y = endpointFiniteInverseLp r y N

theorem endpointFiniteSupportInverse_norm_le (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (y : endpointFiniteSupport r) :
    ‖endpointFiniteSupportInverse r y‖ ≤
      endpointInverseHSBound r * ‖y‖

theorem endpointFiniteSupportInverse_truncation (r : ℝ)
    (y : SobolevCoeff r) (N : ℕ) :
    endpointFiniteSupportInverse r (endpointFiniteSupportTruncation r N y) =
      endpointFiniteInverseLp r y N
```

The displayed subtype witness proves exactly that `sobolevTruncation r N y` vanishes at every `n ≥ N`; its proof term is an implementation detail. `endpointFiniteSupportTruncation` must project definitionally to the literal truncation.

## Exact proof and endpoint checks

If a finite-support vector vanishes at every index `n ≥ M`, then `sobolevTruncation r M y = y` coordinatewise. For two valid bounds `M,N`, compare both finite inverse realizations at `K=max M N` using the audited exact truncation compatibility theorem. Hence `endpointFiniteInverseLp r y M = endpointFiniteInverseLp r y N`; the chosen support bound is immaterial. At a common valid bound `K`, the already audited finite add/smul identities prove that the chosen-bound map is complex-linear. The literal bound `endpointFiniteInverseLp_norm_le` gives the displayed estimate with exactly `endpointInverseHSBound r = 1+1/(r-1/2)`, no changed constant or extra smoothness condition.

For `N=0`, the zero truncation has empty support and inverse value zero. For a vector supported in `0,1,2`, every bound `N≥3` yields the same value. The construction does not yet assert a completed map on all `SobolevCoeff r`, a pointwise representative of an `L²` class, or the frozen negative `Target`.
