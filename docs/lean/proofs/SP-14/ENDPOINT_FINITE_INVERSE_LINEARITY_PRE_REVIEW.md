# SP-14: exact finite inverse linearity for the L² completion

**Status:** source-only mathematical and indexing contract for independent pre-implementation review. No Lean source for this gate exists yet.

## Locks and scope

The frozen `lean-statements/NLA/Statements/SP14.lean` SHA-256 is `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`; the canonical `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex` SHA-256 is `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`. This gate is a prerequisite for the approved `ENDPOINT_INVERSE_PARSEVAL_COMPLETION_PRE_REVIEW.md` SHA-256 `cd170cdb4d4fd1070edfc9185a0475432e8a3db9e83a9d794cb58b08ce6dd4e9`.

The actual finite inverse `endpointFiniteInverse` is locked at `EndpointFiniteRealizationPositive.lean` SHA-256 `427e677daa825ed665935c7e72e59300be85235f9947e14f82f70ed2859a1b91`. Its probability-Haar realization `endpointFiniteInverseLp` is locked at `EndpointFiniteInverseParseval.lean` SHA-256 `923d5323e98301c91c0ad8f57619bc1475ce685b78785e096a495f3cdf0bb0b5`. The finite norm bound source is `EndpointFiniteInverseNorm.lean` SHA-256 `7b2678fd53cededb71dd8e016b75cc56d2c76fbce1ff387a7ebdedb97ed6ec34`; finite truncation is `EndpointFiniteInverseTruncation.lean` SHA-256 `b362fe688ccb49f24bbecb227daccbc90d8eaaae8552b8579732414d515509b6`; tail is `EndpointFiniteInverseTail.lean` SHA-256 `50c51acec1c52097c164bff3ef95d161b9fc49cfb30fc913b56df8bc4e21fe15`.

## Proposed exact public signatures

```lean
theorem endpointFiniteInverseLp_add (r : ℝ)
    (y z : SobolevCoeff r) (N : ℕ) :
    endpointFiniteInverseLp r (y + z) N =
      endpointFiniteInverseLp r y N + endpointFiniteInverseLp r z N

theorem endpointFiniteInverseLp_smul (r : ℝ)
    (c : ℂ) (y : SobolevCoeff r) (N : ℕ) :
    endpointFiniteInverseLp r (c • y) N =
      c • endpointFiniteInverseLp r y N
```

These hold for every real `r` and every `N`, with no `r > 1/2` premise. For `N=0`, all three finite inverses in each identity are zero. They concern the actual `endpointFiniteInverseLp` definition on `AddCircle (2 * Real.pi)` with probability Haar measure, not a replacement sequence model. The source's coefficient is `physicalCoeff r y k = ((k+1)^(-r):ℂ) * y k`; it is complex-linear in `y`. The finite sum `∑ k∈range N, physicalCoeff r y k * endpointInverseMonomial k z` is therefore pointwise complex-linear. Apply the existing continuous-map-to-Lp complex-linear map to those exact pointwise identities. No Fourier sign, normalization factor, or extra scalar enters.

This subgate alone does not define `endpointInverseL2`, prove density, or assert the final `Target`. After independent final audit, it supports the separately approved completion via a finite-support submodule and pinned Mathlib `LinearMap.extendOfNorm` (or an equivalent pointwise-limit construction). Preserve the approved final signatures and constant `endpointInverseHSBound r`; do not weaken them to a pointwise or non-linear extension.
