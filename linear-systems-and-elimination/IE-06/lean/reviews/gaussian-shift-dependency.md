# Gaussian convex-shift dependency: bounded investigation

The completed SubGaussianQuadratic module proves the generic quadratic tail from directional subGaussian MGF bounds. To apply it to the manuscript's conditioned Gaussian rows, those MGF bounds must still be proved. No such bound is silently assumed in a claimed IE-06 proof.

## Exact remaining shift statement

For every natural dimension a, closed convex centrally symmetric set K in real Euclidean a-space, and displacement u, prove
$$
\gamma_a(K-u)\le\gamma_a(K),\qquad K-u=\{x:x+u\in K\}.
$$
Empty K and dimension zero are allowed. Positive Gaussian measure is needed only later, when normalizing the restriction. Central symmetry means x belongs to K if and only if -x belongs to K. Closedness ensures the relevant sets are Borel; the desired application has a closed finite intersection of slabs.

Completing the square and translating Lebesgue measure then give, for every real t and every vector v,
$$
\int_K e^{t\langle v,x\rangle}d\gamma_a(x)
=e^{t^2\|v\|_2^2/2}\gamma_a(K-tv).
$$
For positive measure K, division by gamma(K) yields exactly the directional MGF bound required by SubGaussianQuadratic. Integrability must also be retained; it follows by bounding the nonnegative restricted exponential by its integrable full Gaussian counterpart. Symmetry alone without convexity is insufficient for the shift inequality.

## Smallest general integration theorem supporting this route

Only the midpoint case of Prékopa–Leindler is needed, rather than full marginal log-concavity. In a dimension-a Lebesgue space, for nonnegative measurable integrable real functions f,g,h with
$$
h((x+y)/2)\ge\sqrt{f(x)g(y)}\quad\text{for all }x,y,
$$
the sufficient conclusion is
$$
\int h\ge\sqrt{(\int f)(\int g)}.
$$
For this application set f(x)=rho(x)1_K(x+u), g(y)=rho(y)1_K(y-u), and h(z)=rho(z)1_K(z), where rho is the centered Gaussian density. Convexity of K and the quadratic norm inequality prove the pointwise premise. Central symmetry and Gaussian evenness identify the two integrals on the right. The result is precisely Anderson's shift inequality. All three functions are bounded by the Gaussian density and hence integrable.

This is an exact dependency reduction, not a proof of Prékopa–Leindler. Deriving the required marginal inequality from pointwise log-concavity by directly interchanging logarithm and integral would be invalid. Jensen's inequality in the existing library has the wrong direction to provide this result.

## Pinned-library investigation

Targeted text searches across the pinned Mathlib for Prékopa, Prekopa, Leindler, Brunn–Minkowski, Anderson inequality/theorem, and log-concavity names found no corresponding theorem. The only Brunn–Minkowski occurrence was a bibliographic reference in Analysis/Convex/Intrinsic.lean. Gaussian densities and MGF formulas, finite Jensen, product integration/Fubini, convex-set operations, and translation-invariant Lebesgue measure are available, but they do not alone supply the missing geometric integral inequality.

The relevant source already retained in full-proof-specification.md is [Prékopa's 1973 paper](https://rutcor.rutgers.edu/Prekopa/pdf/SCIENT2.pdf), including its measurability qualifications. An implementation of midpoint Prékopa–Leindler, or a direct proof of the symmetric-convex Gaussian shift theorem, is a substantive further development. No opaque axiom, sorry-backed theorem, externally trusted numerical computation, or assumed source conclusion has been introduced for it.

## Resolved by a checked source port

After this bounded library investigation, an external Apache-2.0 Lean proof was located, inspected, preserved and minimally ported under the existing toolchain. See prekopa-leindler-adoption-contract.md and prekopa-leindler-port-independent-review.md. The resulting GaussianShift and GaussianRestriction modules now prove the shift inequality and the required directional MGF and quadratic tail without assuming either theorem. See gaussian-restriction-implementation.md for exact hashes and validation.
