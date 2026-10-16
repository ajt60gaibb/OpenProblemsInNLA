# TR-06 exact target and numerical inventory — statement draft

Prepared 24 September 2026 for George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology. Original mathematical
proof: Matthew J. Colbrook. The problem and probability model are due to Carlos
Beltrán, Paul Breiding and Nick Vannieuwenhoven. This is AI-assisted preparation,
not a completed formalization or a claim of external human review.

## Immutable source boundary

Repository base: `0689db001ddc4c54f2652ed4b13b753637fef700`.
The canonical page is `tensor-computations/TR-06/README.md`, SHA-256
`f364f4b2ad51065c17d7dd08ea32e729a5d53a8333f0785a11a368165942de6b`.
The complete source proof is
`references/colbrook-unclaimed-2026-09-11/manuscripts/TR-06.md`, SHA-256
`65f9b731628a7a9ab0580d8522cead94bf7e4599ee3c4285e485287d35d451b2`.
Neither source is modified. The original target, status and attribution remain
intact. This file is a proposed formal interface requiring independent review.

## Complete original mathematical target

For EVERY natural order d >= 3, every mode-size vector with n_j >= 2, and EVERY
rank r >= 3 for which the format is generically identifiable over COMPLEX
numbers, let M be the smooth identifiable REAL rank-r tensor locus. Equip its
tangent spaces with the ambient Frobenius norm and M with induced Euclidean
volume dV. Let

    Z = integral_M exp(-||A||_F^2 / 2) dV(A),
    dμ(A) = Z^(-1) exp(-||A||_F^2 / 2) dV(A).

Prove 0 < Z < infinity and finite first expectation under this law of

    κ_ang(A) = ||D(p^r ∘ Ψ)(A)||_2,   p(a) = a / ||a||_F,

where Ψ is any legitimate local ordering of the unique rank-one summands.
The output norm is sqrt(sum_i ||v_i||_F^2). Normalization takes place BEFORE
differentiation. Values on exceptional null sets may be changed only after a
null-set theorem. The distribution is over tensors by volume; it is not obtained
by independently sampling factors or summands. There is no uniform-in-format
constant, higher-moment claim, or ordinary-condition-number claim.

## Concrete candidate definitions

`Tensor 𝕜 d n` is EuclideanSpace over the product of all mode indices; its norm
is precisely the Frobenius norm. `RankOne` requires a NONZERO actual tensor whose
entries are products of mode-vector entries. `Decomposes` requires r such tensors
and their exact sum. `ExactRank` additionally excludes every shorter decomposition.
`Identifiable` quantifies over all pairs of actual decompositions and identifies
them only by a permutation. No factor-scaling ambiguity survives in these actual
tensor objects. The sampling set explicitly conjoins ExactRank and Identifiable.

`GenericComplexIdentifiable` requires a complex coordinate polynomial p, a
COMPLEX exact-rank-r tensor at which p is nonzero, and uniqueness of every complex
exact-rank-r decomposition where p is nonzero. The nonzero witness prevents a
vacuous exceptional set containing the entire secant image. The equivalence to
the original proper-algebraic-exception formulation remains part of review and
semantic proof obligations; no real regularity or integrability is a premise.
The polynomial is not presumed homogeneous. Its nonvanishing set must not be
silently assumed to be a cone. Also, real rank r need not imply complex rank r;
the smaller-complex-rank exceptional set requires a separate null-set proof.

`normalizedTuple` flattens the summand and tensor indices into another genuine
EuclideanSpace, giving the l2 product Frobenius norm. `angularDistance A B` takes
an infimum over ALL actual decompositions of A and B of the Euclidean distance
between their individually normalized tuples. On the identifiable sampling set
it must be proved to equal a finite minimum over permutations. It is an angular
pseudodistance, and correctly vanishes on positive rays. It uses no arbitrary
choice of a globally discontinuous ordering.

`angularSlope A` is the nonnegative extended local slope:

    inf_{ε>0} sup_{B in sampling set, B != A, dist(A,B)<ε}
        angularDistance(A,B) / edist(A,B).

This is a proposed representation of κ_ang, NOT an asserted identity.
`angularSlope_eq_chart_derivative` must prove equality with the ratio
sup_v ||Dg(v)|| / ||Dφ(v)|| for an actual local embedded decomposition chart φ
and g = normalizedTuple ∘ summands. `derivativeRatio_eq_operatorNorm` must identify
that ratio with the operator norm of Dg ∘ (Dφ)^(-1) on range Dφ, with its induced
Frobenius norm. Its inverse is a genuine continuous linear inverse onto the range,
and its injectivity is explicit. No ambient `fderivWithin` default is used.

A `DecompositionChart` is an OpenPartialHomeomorph from a Euclidean coordinate
space into the ENTIRE identifiable rank-r set, with C1 ambient input, C1 summands,
C1 normalized output, and injective input differential. Thus the image is a
relative neighborhood, not merely an immersed subset. `regularSet` collects these
charts; their existence is a conclusion of `regular_locus`, not a hypothesis of
the main theorem. Relating this locus to the canonical smooth local inverse of
the ordered rank-one addition map is a mandatory semantic obligation. The draft
must not be treated as approved while this correspondence is unresolved.

## Measures and required conclusions

The expected dimension is k = r(1 + sum_j(n_j-1)); this formula does not itself
prove a dimension theorem. `tensorVolume` is μHE[k] restricted to the identifiable
real set, using Mathlib's EUCLIDEAN-normalized Hausdorff measure. `regularVolume`
uses its chart-regular subset. `induced_volume_chart` must prove the nonlinear
chart area formula with rectangular volume factor normDet(Dφ). This is the bridge
to actual induced volume; the existing linear-map formula alone is insufficient.

The weight is ENNReal.ofReal(exp(-||A||^2/2)). The normalizing constants are the
actual masses/integrals of these weighted measures. Both input measures are
defined as their own inverse normalization times their own weighted volume.
There is no caller-supplied probability measure or normalizer.

The challenge requires the sampling and regular sets to be measurable, the
removed set to have tensorVolume zero, and regularVolume to be nonzero. It then
requires finite positive normalization, equality of the two normalizations and
probability laws, IsProbabilityMeasure, AE measurability of angularSlope, and
finite ENNReal expectation. Real Bochner-integral default values cannot discharge
this target. Measurability can follow from local derivatives on the full-measure
regular locus without proving the slope semialgebraic everywhere.

## Exact scalar content and computation reduction

The source proof is qualitative. All constants are exact: d>=3, n_j>=2, r>=3;
k=r(1+sum(n_j-1)), s=k-1; Gaussian coefficient 1/2; normalization exponent -1;
homogeneity exponent -1; radial volume power k-1 and numerator power k-2.
The radial domain is t in (0,infinity), excluding zero. k>1 is to be proved from
the admitted format. The numerator and denominator radial integrals are

    integral_0^infinity t^(k-2) exp(-t^2/2) dt,
    integral_0^infinity t^(k-1) exp(-t^2/2) dt.

Both follow from Mathlib's `integrableOn_rpow_mul_exp_neg_mul_sq` once the exact
exponent thresholds are established. No Gamma evaluation, decimal estimate,
subdivision, interval cover, numerical eigenvalue computation, or floating-point
certificate is needed. If a numerical certificate is later introduced it must
select `leancert (trust := kernel)` and survive `#assert_trust kernel` and
Comparator; a decorative scalar calculation is not evidence for this target.

The difficult numerator input is the finite angular link integral, obtained by
bounded semialgebraic graph volume and the graph Jacobian estimate. Boundedness
alone is insufficient. Its finite-volume, area, generic regularity and polar
bridges must be PROVED for the actual tensor model. No theorem-valued structure
field or additional assumption may replace them in the complete target.

## Current proof boundary

Definitions and the five draft Challenge signatures elaborate on Lean 4.33.1.
Challenge placeholders prove nothing. There is no Solution, no accepted final
statement review, no TR-06 axiom report, no LeanCert certificate, and no Comparator
run. Formalization remains incomplete, and canonical status remains Solved.
