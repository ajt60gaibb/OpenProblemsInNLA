# Proposition 3.2

**Proposition 3.2 and Lemmas 3.3–3.5 are fully proved and Lean-checked.**

Base: `fdf905eea2cee5cf2f90331d4d4711bdfee8ff4b` on
`codex/fr05-partial-formalisation`. The source PDF still has SHA-256
`d1be40e71e492fc16aed05ca8e71153a8e2114a2af8218a7700a4ec3c6897254`.

`NLA.FR05.proposition_3_2` proves the following bound for the concrete source likelihoods:

```lean
∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, 2 ≤ D ∧
  ∀ (M : ℕ) (hM : 2 ≤ M), D ≤ M →
    sourceLikelihoodL2 M hM ≤ C / M
```

Import `NLA.FR05.LikelihoodComparison` to access the completed theorem and its prerequisites.

## Checked components

| Module | Content |
| --- | --- |
| `Densities/SourceLikelihood` | Equations (3.1), (3.3), and (3.4); measurable nonnegative densities; `g ≤ exp(1) M^52`, `r ≤ 4`; covariance limit and strict gap for every `M ≥ 2`. |
| `Gaussian/RadialMoments` | Exact radial Laplace transform in every complex dimension, polynomial-exponential integrability, and first two tilted radial moments in dimension two. |
| `Densities/SourceReferenceMoments` | Normalization of (3.4), its probability law, exact radial Laplace transform and first two moments, all radial moments finite, and a uniform exponential-moment bound. |
| `Densities/SourceSymmetry` | Gaussian unitary invariance; independent phase rotations and coordinate swap preserve both concrete densities and the reference law. Integrability of coordinates and quadratic products; centering, zero pseudocovariance, and reference covariance `v I₂`. |
| `Gaussian/GaussianSquaredRadius` | Polar-coordinate integral; the squared magnitudes of the existing complex Gaussian law are independent Exp(1) variables. |
| `Gaussian/RadialMoments` | Integrability and exact exponential tail integrals for nonnegative quadratic polynomials. |
| `Densities/SourcePlantedRadial` | Actual density (3.1) reduces to the radial density (3.2), by integrating the imbalance interval; polynomial and exponential integrability. Planted normalization, probability law, exact radial Laplace transform and mean `2v`, covariance `v I₂`, zero mean/pseudocovariance, phase/swap symmetry, and uniform exponential moment. |
| `Densities/SourceDensityMoments` | Shared moment interface for the actual correlation-kernel densities: normalized mass, integrable first/second moments, matched covariance, and a common exponential-moment bound. |
| `Likelihood/HaarLikelihood` | Compact unitary group, normalized Haar probability, orthonormal first two columns, and the actual likelihood integrals (3.5); measurability and pointwise bounds. Integrability of all three products under the existing Gaussian frame law; the exact squared-difference integral identity. Fubini and iid row factorization for bounded measurable mixture likelihoods. |
| `Gaussian/GaussianFrameRows` | The existing complex Gaussian frame law equals the product of the branch's existing Gaussian row laws. |
| `Likelihood/SourceCorrelation` | Actual row correlation kernels; measurability, bounds, and integrability; the source second-moment formula in Haar pair coordinates; exact L² integral and its absolute-difference bound. |
| `Overlap/Overlap` | Actual two-frame overlap law as a Haar pushforward; the two-by-two determinant identity and Gaussian upper bound. |
| `Gaussian/GaussianGram` | Exact Gaussian characteristic function; equal Gram matrices give equal joint projection laws, including singular cases and different ambient dimensions. |
| `Likelihood/SourceOverlapKernel` | Joint law determined by the block matrix `[[I,K],[K*,I]]`; measurable overlap kernels; equation (3.17), L² overlap identity, and absolute-difference bound. |
| `Overlap/OverlapGaussian` | Lebesgue integrability and exact eight-dimensional quartic Gaussian rescaling; the local prefactor yields `M⁻¹`. |
| `Likelihood/CanonicalKernelBounds` | Cancellation of matched quadratic terms; boundary factorization and bound; exponential tails dominate every fixed polynomial. |
| `Cone/Phase`, `Cone/ConeGeometry` | Exact reciprocal circle integrals, normalized phase measure, cone bases, and the discriminant identity. |
| `Cone/ConeGeometry`, `Cone/ConeImageEstimates` | Operator-norm and determinant estimates; phase-average upper bound and weighted radial lower bound. |
| `Cone/ConeImageEstimates`, `Cone/ConeSchur`, `Cone/ConePhaseAverages` | Rotated overlap, conditional covariance, radial correction, and the final exponential estimate. |
| `Gaussian/ComplexGaussianDensity`, `Cone/ConeGaussianMoments`, `Gaussian/ScalarGaussianMoments` | The existing Gaussian law's scalar Lebesgue density, affine change of variables, and exact quadratic/fourth moments. |
| `Cone/ConePhaseAverages`, `Cone/ConeRayDensity` | Explicit Gaussian likelihood ratio, unitary invariance, restricted density identity, and integrable cone-ray moments. |
| `Cone/ConeCorrelation` | The cone probability measures, actual correlation integral, integrability, and Lemma 3.3 with the exact source constants. |
| `Gaussian/GaussianConditionalDensity`, `Overlap/OverlapCholesky` | The explicit likelihood ratio is the density of the Gaussian with covariance `[[I,K],[K*,I]]`; it agrees with the original row kernel. |
| `Likelihood/SourceKernelMarginals`, `Likelihood/CanonicalKernelBounds` | Gaussian marginals, nonnegativity, and the uniform `(exp(1)+4) M^52` bound. |
| `Likelihood/KernelMoments`, `Likelihood/ScalarTaylor`, `Likelihood/KernelMatrixAlgebra`, `Likelihood/KernelLocalEstimates` | Exact quadratic coefficient, sign cancellation, and an explicit uniform fourth-order remainder for operator norm at most `1/128`. |
| `Gaussian/GaussianPolarLaw`, `Cone/ConeMagnitudeCoordinates`, `Densities/PlantedPolarLaw`, `Cone/PlantedConeParameters`, `Cone/PlantedConeDomination`, `Likelihood/PlantedGlobalBound` | Polar and radius/imbalance changes of variables; domination by averaged cone laws; planted global bound from Lemma 3.3. |
| `Gaussian/GaussianQuadraticIntegral`, `Likelihood/ReferenceKernelExact`, `Overlap/Spectrum` | Exact reference determinant formula and its global estimate via log concavity. |
| `Overlap/Spectrum`, `Likelihood/GaussianConditionalPair`, `Likelihood/GaussianKernelCauchySchwarz` | Shared Gaussian representation and Cauchy–Schwarz for arbitrary overlap matrices. |
| `Likelihood/UniformKernels` | Lemma 3.4 for all density pairings and every `M ≥ 2`; bounds transported to the original kernels. |
| `Overlap/HaarCorner`, `Overlap/UnitaryCompletion`, `Gaussian/GaussianSphere` | Haar overlap as a unitary corner; orthonormal completion; normalized Gaussian representation of a Haar column. |
| `Gaussian/RadialMoments`, `Gaussian/GammaSimplexLaw`, `Gaussian/SimplexProjectionLaw` | Gaussian energy has the Gamma law; exact simplex/radius Jacobian and normalized magnitude density. |
| `Gaussian/SimplexProjectionLaw`, `Gaussian/NormalizedProjectionLaw`, `Gaussian/ComplexVectorDensity` | Complex spherical projection density, including arbitrary orthonormal projections and its Lebesgue normalization. |
| `Overlap/HaarColumnConditioning`, `Overlap/RankOneSphereGeometry` | Haar invariance gives the joint first-two-column law through sequential sphere projections. |
| `Gaussian/ComplexVectorDensity`, `Overlap/RankOneSphereGeometry`, `Overlap/Spectrum`, `Overlap/HaarColumnConditioning`, `Overlap/HaarOverlapDensity` | Elliptical density, determinant identity, exact operator-ball support, coordinate Lebesgue measure, and density product. |
| `Overlap/HaarOverlapDensity` | Lemma 3.5 with the exact constant for every `M ≥ 4`. Volume-preserving real coordinates, Gaussian integrability, and exact quartic rescaling for the matrix Lebesgue measure. |
| `Likelihood/LikelihoodDensityBounds` | Fixed local radius, uniform Gaussian bound, and weighted kernel-difference estimate. Boundary control and an integrable majorant with an exponentially decaying tail. |
| `Likelihood/LikelihoodIntegration` | Actual pairwise second-moment comparisons and `proposition_3_2`. |
| `LikelihoodComparison` | Public import boundary for the completed proof. |

The Gaussian row factorization and overlap integral (3.17) use the original
`standardComplexGaussianFrame` and `sourceOverlapLaw` measures. They hold for
every `M ≥ 2`, with no assumed kernel estimates. Equal overlaps give equal
joint projection laws, proved using the branch's scalar Gaussian projection
theorem and characteristic functions. The overlap kernels agree with the
actual row kernels on realizable overlaps and are zero elsewhere; measurable
descent establishes their Borel measurability. Lemma 3.4 now supplies the sharper bounds, including the original row-kernel Taylor expansion.

For the reference density, with `S = |z₁|² + |z₂|²` and `v = sourceVariance M`,
the new law is proved to have total mass one and
`E[exp(t S)] = (1 - v t)⁻²` for every `t < v⁻¹`. Its first two radial moments
are `E[S] = 2v` and `E[S²] = 6v²`; for `M ≥ 2`, `E[exp(S/4)] ≤ 16/9`.

Both concrete densities now have normalized probability laws, zero mean,
zero pseudocovariance, and covariance `v I₂`. Independent phase rotations of
each coordinate and coordinate swap preserve both laws. Integrability is proved
for their coordinates and quadratic products.

For the planted law, `E[S] = 2v` and `E[exp(S/4)] ≤ 4 exp(1)` for every
`M ≥ 1`; its exact Laplace transform is proved for all `t < 1`. The density
normalization follows from the original Gaussian measure: its squared magnitudes
are independent Exp(1) variables, and the imbalance cutoff becomes an interval
of length `ε S`. This cancels the reciprocal-radius term and yields (3.2).
No normalization or covariance premise is assumed.

`Densities/SourceDensityMoments` exports these identities directly for `sourceDensity`,
the same functions used by the actual correlation kernels. For both density kinds
and all `M ≥ 2`, the common exponential-moment bound is `4 exp(1)`.
The cone estimate is now exported as `NLA.FR05.lemma_3_3`:

```lean
coneCorrelation K t s ≤
  Real.exp (t ^ 2 + s ^ 2 - overlapOperatorNorm K ^ 2 / 2000) *
    overlapDeterminant K ^ (-(1 / 4 : ℝ))
```

Its only hypotheses are `overlapOperatorNorm K < 1`, `|t| ≤ 1/4`, and
`|s| ≤ 1/4`; `sourceEta = 1/100`. Here `coneCorrelation` is the integral
over the actual product `coneMeasure t × coneMeasure s`, with scalar density
`[(1-η)+η|x|²] π⁻¹ exp(-|x|²)`. The Gaussian likelihood ratio is represented
by its explicit conditional-density formula using `I-KᴴK`.
`coneCorrelation_eq_moment` proves the connection to the phase-averaged
conditional moments, and `integrable_coneCorrelation` establishes finiteness.

The proof uses the slightly weaker radial correction
`D ≥ (3ρ²/32 - 2(t²+s²)) I` instead of the paper's `ρ²/10`.
This simplifies a pointwise inequality while retaining the exact final
constant: `η(1-η)·3/32 - 4η² = 169/320000 > 1/2000`.
No cone integral identity or phase estimate is assumed.
`sourceDensityCorrelation_eq_integral_canonical` identifies the explicit-density integral
with the canonical Gaussian expectation. `sourcePairKernel_eq_densityCorrelation`
connects it to the original row kernel; the descended kernel agrees on realizable overlaps.

`NLA.FR05.lemma_3_4` proves, for every `M ≥ 2`, both density kinds, and `ρ < 1`:

- `0 ≤ ρ_ab(K) ≤ exp(2δ + 2ε² - ρ²/2000) Δ^(-1/4)`;
- `ρ_ab(K) ≤ (exp(1)+4) M^52`;
- when `ρ ≤ 1/128`, the error in `1 + (1-v_M)² F` is at most
  `11000 * kernelMomentConstant 4 * F²`, where `F = ‖K‖_F²`.

The local scalar estimate now factors the even exponential as `exp(-A) cosh(B)`;
separate expansions give constant `304` in place of `5000`. The final Taylor
constant `11000` above is retained, so the later radius and integration bounds
do not change.

The remainder constant is absolute. The proof includes the Gaussian density bridge,
the planted cone decomposition, the exact reference determinant, and the shared-Gaussian
Cauchy–Schwarz argument. No analytic estimate is assumed.

`NLA.FR05.lemma_3_5` proves that, for every `M ≥ 4`, the existing
`sourceOverlapLaw M` equals coordinate Lebesgue measure weighted by

```text
((M-1)(M-2)²(M-3) / π⁴) · det(I₂-KK*)^(M-4) · 1_{‖K‖op < 1}.
```

The proof derives the spherical projection law from normalized complex Gaussians,
then uses Haar invariance to average the second column in the first column's
orthogonal complement. An explicit triangular change of variables supplies the
elliptical density. The determinant identity and support equivalence complete
the formula, including `M = 4`. No spherical or Haar density is assumed.

The boundary estimate reserves **15** factors:
`ρ^(4M-5) Δ^(M-4) = ρ^15 (ρ^4 Δ)^(M-5) Δ`, for `M ≥ 5`.
This avoids fractional determinant powers in the factorization. Its larger polynomial
prefactor is still absorbed by exponential decay.

## Completed integration

Put `R = sourceTaylorConstant` and
`r = min (1/128) (1/(1600(R+1))) > 0`. The proved covariance gap gives,
for `M ≥ 1600`, `‖K‖op ≤ r`, and every exponent `n ≤ 4M`,

```text
ρ_ab(K)^n Δ^(M-4) ≤ exp(-M F/400),   F = ‖K‖_F².
```

The matched Taylor expansions and the density prefactor bound `c_M ≤ M⁴`
therefore bound the weighted kernel-power difference by
`8R M⁵ F² exp(-M F/400)`. A volume-preserving coordinate map identifies this
matrix integral with the eight-dimensional Euclidean integral, giving
`8R I/M`, where `I = ∫ F² exp(-F/400) dK` is proved finite.

Outside the local ball, the reserved-factor estimate bounds each weighted
kernel by `C M⁷⁸⁴ exp(-cM)`, with `c = r²/1000 > 0`. On the operator ball,
`F < 2`, so an integrable multiple of `exp(-F)` controls the tail.
The integrated tail is at most `1/M` beyond a proved threshold.

Thus every kernel comparison is bounded by `sourcePairComparisonConstant/M`,
where `sourcePairComparisonConstant = 8R I + 1 > 0`.
`source_second_moment_comparisons` exports this for the original Gaussian
frame likelihoods. The exact L² identity yields `proposition_3_2` with
constant `3 * sourcePairComparisonConstant`. No analytic estimate is assumed.

## Archived Proposition 3.2 verification

All 100 development modules were checked with Lean 4.33.1 against the pinned Mathlib
revision. `verification/proposition32/Inspect.lean` audits the principal declarations;
`check.log` records their transitive axioms. Only `propext`, `Classical.choice`,
and `Quot.sound` are used. There are no new `sorry`, custom axioms, or native
decision proofs.

The separate `Solution` import closure was not rebuilt in this checkout.
Proposition 3.1 and the full FR-05 theorem remain outside this result. No Comparator
run, independent review, or full FR-05 verification is claimed.

The preceding paragraph describes the archived Proposition 3.2 checks only.
The current development now also proves Proposition 3.1 and the full FR-05
bound and limit, with a successful local `Solution` build. See
[FINAL_ASSEMBLY.md](FINAL_ASSEMBLY.md) and
[the current local audit](verification/library-cleanup/README.md). Independent review
and the isolated Linux Comparator/kernel check are still separate requirements.
