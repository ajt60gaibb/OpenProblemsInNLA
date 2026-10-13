# SP-14: pointwise finite endpoint realization from the frozen Fourier integral

**Status:** source-locked mathematical and exact-mode pre-implementation contract for independent review. No Lean source for this gate has been written. **Author:** `/root/sp14_base_proof`, 10 October 2026.

## Frozen sources and scope

| Source | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| `docs/lean/proofs/SP-14/ENDPOINT_FINITE_REALIZATION_PRE_REVIEW.md` | `d949dca7a704f48139a5615d30db305f92fde00c0e28125ef33f24b40d47677f` |
| `lean-statements/NLA/Proofs/SP14/EndpointFiniteRealizationPositive.lean` | `427e677daa825ed665935c7e72e59300be85235f9947e14f82f70ed2859a1b91` |
| `lean-statements/NLA/Proofs/SP14/EndpointFiniteRealizationNegative.lean` | `548ba841c488db2b0f20fd48750d3f90bb795700b7551bc49b0b4f616bf9a2bc` |
| `lean-statements/NLA/Proofs/SP14/EndpointCircleSeries.lean` | `a3ea7def39f80cb3b898a0b68c81146d51cf96541f2e1ca8c05e701764288162` |
| `lean-statements/NLA/Proofs/SP14/EndpointCircleFourier.lean` | `a086299a49f93533e49d101c4bc0f2a2d2d43bbcf588309814fbc7b828430e3b` |

Both finite coefficient modules direct-build with LeanCert kernel assertions and only `[propext, Classical.choice, Quot.sound]`; the negative module awaits a separate imported final audit. This contract assumes their exact public theorems, and implementation must wait for that audit and independent approval of this contract. The canonical source's finite formula is `Ey=g₀V`; the proposed result realizes it as equality of genuine continuous functions on the circle, only for finitely supported inputs.

## Exact public Lean statements

The generic uniqueness gate must concern the original totalized interval-integral definition, with continuity making its integrals genuine:

```lean
theorem continuous_eq_of_forall_FourierCoefficient_eq
    (f g : Circle → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hcoeff : ∀ p : ℤ, FourierCoefficient f p = FourierCoefficient g p) :
    f = g
```

The source-specific conclusion is exactly the previously reviewed finite realization statement, including its `N=0` endpoint:

```lean
theorem endpointCircleRealization_eq_finiteInverse
    (r : ℝ) (hrHalf : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (y : SobolevCoeff r) (N : ℕ)
    (hy : ∀ k : ℕ, N ≤ k → y k = 0) (z : Circle) :
    endpointCircleRealization r hrHalf hr1 y z =
      endpointBaseSymbol z * endpointFiniteInverse r y N z
```

`endpointFiniteInverse` is the audited finite sum `∑ k<N physicalCoeff r y k * endpointInverseMonomial k z`; no replacement Laurent series or abstract coefficient functional is allowed. Do not add a nonvanishing premise for `endpointBaseSymbol`, since it is zero at the endpoint.

## Mathematical derivation and normalization obligation

For continuous `f,g : Circle → ℂ`, pull back through Mathlib's homeomorphism `AddCircle.homeomorphCircle' : AddCircle (2π) ≃ₜ Circle`. Its value on real class `t` is `Circle.exp t`. In pinned Mathlib, `AddCircle.fourierCoeff_eq_intervalIntegral` at period `T=2π`, start `0`, gives

\[
\operatorname{fourierCoeff}(f\circ\mathrm{homeomorphCircle'})(p)
=\frac1{2\pi}\int_0^{2\pi}e^{-ipt}f(\mathrm{Circle.exp}\,t)\,dt.
\]

The right side is *definitionally the intended value* only after proving the normalization/sign bridge to the frozen `FourierCoefficient`, including `fourier (-p)` and the commute of scalar multiplication with complex multiplication. This bridge is a required Lean lemma; invoking AddCircle uniqueness without it would change the target.

The normalized Haar measure on `AddCircle (2π)` has full support. Mathlib's `AddCircle.fourierBasis_repr` identifies the `L²` Fourier-basis coordinates with `AddCircle.fourierCoeff`. If all frozen coefficients of `f` and `g` agree, the bridge makes all coordinates of their pullback difference zero. Hilbert-basis injectivity yields equality almost everywhere. Continuity and full support upgrade this to pointwise equality, then the homeomorphism's surjectivity gives `f=g`. Equivalently, the implementation may use the dense Fourier span and continuous linear functionals, but it must prove the same literal integral bridge and pointwise conclusion.

For the source-specific theorem, `continuous_endpointCircleRealization` gives continuity on the left. `continuous_endpointBaseSymbol` and finite continuity of `endpointInverseMonomial` give continuity on the right. Every integer `p` falls into exactly one branch: `p=(k:ℤ)` for `k≥0` (including zero), or `p=-((t+1:ℕ):ℤ)` for `t≥0`; the branches do not overlap. `endpointCircleRealization_fourier_nonneg` and `endpointFiniteInverse_fourier_nonneg` equate the former branch with `physicalCoeff r y k`. `endpointCircleRealization_fourier_neg` and `endpointFiniteInverse_fourier_neg` equate the latter branch with `physicalCoeff r (endpointNegativeOperator r (by linarith) hr1 y) t`. Generic uniqueness then yields the displayed equality at every `z : Circle`.

## Exact endpoint checks and limits

At `N=0`, `hy` forces every `y k=0`, both Fourier branches vanish, and `endpointFiniteInverse` is the empty sum; the theorem says the continuous realization is pointwise zero. For a unit physical input at `k=0`, the polynomial is `V=1`, so `g₀V` has coefficients `1,1/2,-1/8` at `0,-1,-2`. For a unit physical input at `k=1`, `V=z-1/2`, and coefficients at `1,0,-1,-2` are `1,0,-3/8,1/8`. These exact rational checks are inherited from the approved finite-realization contract; they test the sign and `t+1` shift, not an approximation.

The theorem is only finite-input pointwise consistency of the canonical endpoint extension. It does not show the infinite inverse polynomial converges, that an infinite extension vanishes at `z=-1`, either-sided nonextension, perturbed-background invertibility, stage solvability, the canonical spectral gap, or the frozen negative `Target`. No statement/target, problem identity, or catalog file may be changed. After independent mathematical review, implement in an unimported module, freeze its SHA, and require a separate imported LeanCert exact-signature/kernel audit before aggregate import.
