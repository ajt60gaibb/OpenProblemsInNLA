# SP-14: actual finite inverse Parseval and normalized-circle L² completion

**Status:** frozen mathematical, numerical, and indexing contract for independent pre-implementation review. **Author:** `/root/sp14_base_proof`, 11 October 2026. No Lean source for this new gate has been written.

## Source locks and scope

| Source | SHA-256 |
| --- | --- |
| Frozen `lean-statements/NLA/Statements/SP14.lean` (`Target`, `FourierCoefficient`) | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Canonical `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, endpoint-extension lemma, lines 856–902 | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| `EndpointFiniteRealizationPositive.lean` (`endpointFiniteInverse`) | `427e677daa825ed665935c7e72e59300be85235f9947e14f82f70ed2859a1b91` |
| `EndpointFiniteInverseFourier.lean` (actual normalized integral coefficients) | `6ed1c17c76bec2391a6070f6c5593a020526c395b2312c0ea655b8b131c1d219` |
| `EndpointInverseHSScalar.lean` (`S_r`, `B_r`, `S_r ≤ B_r²`) | `1cb184a240b5486f6063d39972b4a5f2e323d746fc048334364ec7f4e5e723a9` |
| `EndpointFiniteInverseEnergy.lean` (finite coefficient energy) | `69e064c5927281ed8266fa3bd338227b3838d6e9608f24dc295e7565ac982286` |
| `WeightedSobolevPhysical.lean` (literal weighted coefficient map) | `ea0166080ec91c5df4da14e2f38eca5fc2a7f9271866099aad1fb8f46e5ba109` |
| `WeightedSobolevOperators.lean` (literal truncation) | `f0368eb90ab2af9bdbdce1405c1bae511e4c1868ff95015d575cde65fd07b0f1` |
| `EndpointNegativeTruncation.lean` (strong convergence of literal truncation) | `7454b7819bae6d5292bcaf53b482371adda48b7f8d55640395e542d08db47c06` |
| Pinned Mathlib `Mathlib/Analysis/Polynomial/Fourier.lean` (polynomial Parseval) | `8a7f21a29790b5b61c181bbf39bc4b90f94b78d8c80c969c900744fc41318d6d` |
| Pinned Mathlib `Mathlib/Analysis/Fourier/AddCircle.lean` (probability Haar, Fourier, Parseval) | `87fe0972a4370b6fdd14c327855f4e7ab98edf37e9e2ebb5182ab0f676bc16b2` |

The manuscript claims that the **same** triangular inverse (V=T(g_0)^{-1}y) extends from polynomial inputs to (H^r\to L^2(\mathbb T)) for (r>1/2). The exact finite inverse is the already frozen `endpointFiniteInverse r y N`; its analytic Fourier coefficient is `endpointFiniteInverseCoeff r y N d`. This contract supplies finite Parseval, the norm bound with the explicit sufficient constant (B_r=1+1/(r-1/2)), and completion of that actual polynomial map. It is distinct from the already proved (E y=g_0V) circle realization. It does not assert a pointwise value for the arbitrary (L^2) limit or prove the final negative `Target`.

## Exact circle norm and Fourier normalization

Use Mathlib's additive circle `AddCircle (2 * Real.pi)` with its probability Haar measure `AddCircle.haarAddCircle`; the local period instance is `Fact (0 < 2 * Real.pi)` from `Real.two_pi_pos`. The map `AddCircle.toCircle` sends the class of real (t) to the frozen `Circle.exp t` because `toCircle_apply_mk` has factor (2\pi/(2\pi)=1). For every continuous (f:\mathrm{Circle}\to\mathbb C), the integral of (\|f\circ\mathrm{toCircle}\|^2) against probability Haar measure equals

\[
\frac1{2\pi}\int_0^{2\pi}\|f(\mathrm{Circle.exp}\,t)\|^2\,dt.
\]

The right side uses the real interval integral and matches the manuscript's normalized circle (L^2) convention. For (p\in\mathbb Z), Mathlib `fourierCoeff` on this additive circle uses the same negative exponential sign as frozen `NLA.Statements.SP14.FourierCoefficient`, by `fourierCoeff_eq_intervalIntegral` and `toCircle_apply_mk`; the scalar multiplier is (1/(2\pi)), with no extra (2\pi) or reversed mode. The implementation must prove this bridge where used, not silently identify two definitions.

Let `endpointFiniteInverseLp r y N` be the `Lp ℂ 2` representative of the continuous additive-circle function

\[
\theta\longmapsto \operatorname{endpointFiniteInverse}(r,y,N)(\operatorname{AddCircle.toCircle}\theta).
\]

The exact finite Parseval claim is, for **every real** (r), every weighted input (y), and every (N\ge0),

\[
\|\operatorname{endpointFiniteInverseLp}(r,y,N)\|_2^2
=\frac1{2\pi}\int_0^{2\pi}
  |\operatorname{endpointFiniteInverse}(r,y,N)(\mathrm{Circle.exp}\,t)|^2\,dt
=\sum_{d=0}^{N-1}|\operatorname{endpointFiniteInverseCoeff}(r,y,N,d)|^2.
\]

The first equality is the exact probability-Haar/interval bridge; the second follows either by finite orthogonality of the frozen positive `Circle.exp` modes or by identifying a complex polynomial with the finite inverse and applying pinned `Polynomial.sum_sq_norm_coeff_eq_circleAverage`. The `d≥N` coefficients and every negative coefficient are zero by the audited finite Fourier module. The zero-length case (N=0) has all three expressions equal to zero.

## Proposed public Lean signatures

The exact output type uses the pinned normalized Haar measure. A local `Fact (0 < 2 * Real.pi)` may be declared in the module; the definitions must not use unnormalized `volume` on `AddCircle`.

```lean
noncomputable def endpointFiniteInverseAddCircle (r : ℝ)
    (y : SobolevCoeff r) (N : ℕ) :
    C(AddCircle (2 * Real.pi), ℂ)

noncomputable def endpointFiniteInverseLp (r : ℝ)
    (y : SobolevCoeff r) (N : ℕ) :
    MeasureTheory.Lp ℂ 2 (AddCircle.haarAddCircle (T := 2 * Real.pi))

theorem endpointFiniteInverse_interval_parseval (r : ℝ)
    (y : SobolevCoeff r) (N : ℕ) :
    ((1 / (2 * Real.pi) : ℝ) *
      ∫ t in (0 : ℝ)..(2 * Real.pi),
        ‖endpointFiniteInverse r y N (Circle.exp t)‖ ^ 2) =
      ∑ d ∈ Finset.range N, ‖endpointFiniteInverseCoeff r y N d‖ ^ 2

theorem endpointFiniteInverseLp_norm_sq (r : ℝ)
    (y : SobolevCoeff r) (N : ℕ) :
    ‖endpointFiniteInverseLp r y N‖ ^ 2 =
      ∑ d ∈ Finset.range N, ‖endpointFiniteInverseCoeff r y N d‖ ^ 2

theorem endpointFiniteInverseLp_norm_le (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (y : SobolevCoeff r) (N : ℕ) :
    ‖endpointFiniteInverseLp r y N‖ ≤
      endpointInverseHSBound r * ‖y‖

theorem endpointFiniteInverseLp_truncation (r : ℝ)
    (y : SobolevCoeff r) (M N : ℕ) (hMN : M ≤ N) :
    endpointFiniteInverseLp r (sobolevTruncation r M y) N =
      endpointFiniteInverseLp r y M

theorem endpointFiniteInverseLp_tail_le (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (y : SobolevCoeff r)
    (M N : ℕ) (hMN : M ≤ N) :
    ‖endpointFiniteInverseLp r y N - endpointFiniteInverseLp r y M‖ ≤
      endpointInverseHSBound r * ‖y - sobolevTruncation r M y‖

noncomputable def endpointInverseL2 (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) :
    SobolevCoeff r →L[ℂ]
      MeasureTheory.Lp ℂ 2 (AddCircle.haarAddCircle (T := 2 * Real.pi))

theorem endpointInverseL2_truncation (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (y : SobolevCoeff r) (N : ℕ) :
    endpointInverseL2 r hrHalf (sobolevTruncation r N y) =
      endpointFiniteInverseLp r y N

theorem endpointInverseL2_norm_le (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) :
    ‖endpointInverseL2 r hrHalf‖ ≤ endpointInverseHSBound r

theorem endpointFiniteInverseLp_tendsto (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (y : SobolevCoeff r) :
    Filter.Tendsto (fun N : ℕ => endpointFiniteInverseLp r y N)
      Filter.atTop (nhds (endpointInverseL2 r hrHalf y))
```

The first `def` must have value `fun θ => endpointFiniteInverse r y N (AddCircle.toCircle θ)`; the second must be its exact `ContinuousMap.toLp 2 haarAddCircle ℂ` class. Continuity of the finite inverse is an implementation obligation because the existing helper in `EndpointFiniteRealizationPointwise.lean` is private. Lean's exact constructors, instance arguments, and namespace qualifications may need elaboration adjustments that leave these carriers and functions unchanged. If a different `Lp` representation is chosen, a new pre-reviewed contract must explicitly prove its isometry with this probability-Haar carrier and retain the interval equality above. Theorems may be split into small audited modules in the listed order. The public operator must be the completion of the frozen finite inverse, not an unrelated bounded map.

## Proof obligations and exact small cases

1. The finite additive-circle function is continuous. Bridge `AddCircle.toCircle_apply_mk` at (T=2\pi) to `Circle.exp` at every real parameter, and bridge Haar integration to the displayed interval integral. Neither bridge may assume equality of unnormalized `volume` and `haarAddCircle`.
2. Finite Parseval uses degrees (0,\dots,N-1), with coefficient (v_{N,d}=\sum_{k=d}^{N-1}b_{k-d}(k+1)^{-r}y_k). This is the actual `endpointFiniteInverseCoeff`, with no index reversal, no modulus of (b_l) before taking the final norm, and no negative modes. The source does not require pointwise convergence of the infinite inverse.
3. The independently audited finite energy theorem gives `‖finiteLp‖² ≤ S_r‖y‖²`; `S_r≤B_r²` and (B_r>0) give the stated unsquared norm bound for every (r>1/2). There is no extra condition (r<1) in this inverse estimate.
4. For (M≤N), exact finite triangular compatibility is (V_N(T_M y)=V_M(y)), using `physicalCoeff_truncation`; finite inverse is complex-linear in (y). Therefore the displayed tail inequality is exact with constant (B_r). Since `tendsto_sobolevTruncation r y` is already kernel-audited, the finite inverse sequence is Cauchy in the complete probability-Haar `Lp ℂ 2`. Its limit gives the **unique** bounded complex-linear extension satisfying the truncation identity and norm bound.
5. The `Lp` norm is a norm on almost-everywhere classes; the completion theorem claims only an (L^2) class. Fourier-coordinate identification of that class with (\sum_{k=d}^{\infty}b_{k-d}(k+1)^{-r}y_k) for (d≥0), and zero for negative (d), is a subsequent gate requiring row absolute summability and continuity of Fourier coefficients on `Lp`. No evaluation of `endpointInverseL2 r hrHalf y` at a particular circle point is proposed.

Numerical/indexing witnesses:

| Input / length | Analytic coefficients of (V_N) | Normalized (L^2) norm squared |
| --- | --- | --- |
| (N=0), any (y) | empty | (0) |
| (N=1) | ((a_0)) | \(|a_0|^2\) |
| (N=2) | \((a_0-a_1/2,a_1)\) | \(|a_0-a_1/2|^2+|a_1|^2\) |
| (N=3) | \((a_0-a_1/2+3a_2/8,a_1-a_2/2,a_2)\) | sum of these three squared moduli |
| (N=2), (y=e_1) | \((-2^{-r}/2,2^{-r})\) | \((5/4)2^{-2r}\) |
| (N=3), (y=e_2) | \((3\cdot3^{-r}/8,-3^{-r}/2,3^{-r})\) | \((89/64)3^{-2r}\) |

The first three Hilbert–Schmidt columns are (1), \((5/4)2^{-2r}\), \((89/64)3^{-2r}\). At (r=3/4), (B_r=5) and the sufficient operator norm bound is (5); at (r=7/8), (B_r=11/3). These are exact rational constants from the pre-reviewed scalar gate, not optimal constants or values fixed by the manuscript.

This leaves the actual perturbed-background inverse with compatible two-level bounds, nonlinear jet selection, both-sided nonextension of the packet symbol, selected-section multiplicities, canonical gap, and frozen negative `Target` open.
