# Gaussian overcrowding A3 assembly

Root independently approved the full argument and this exact contract before
implementation on 2026-10-06. For natural n,j with 4≤j<n and 0<theta≤1,
under the literal square iid standard Gaussian law, prove

`P[Spectral.singularValue G (n-j-1) ≤ j*theta/(4*exp 1*sqrt n)]
 ≤ ENNReal.ofReal(n^(j+1)*theta^((j:real)^2/4))`.

The singular value uses genuine Euclidean operators and zero-based indexing;
it is the source one-based sigma_(n-j). The threshold has universal constant
1/(4e). The exponent on theta is real j²/4, retaining fractional exponents.

Use q=(j+3)/4, r=j+1-2q, m=n-2q. The first m rows have the actual gaussianRect
m n pushforward law; prove this explicitly from independent coordinates.
The row-restricted Gram matrix is positive definite almost everywhere by the
proved rank law. The deterministic GaussianOvercrowdingSpectral lemma supplies
an actual inverse-Gram principal minor at least (t^(2r))⁻¹/choose(m,r).
Apply GaussianPrincipalTail.principal_union_tail, discard only the proved
null exceptional set, and simplify with the independently reviewed exact
GaussianOvercrowdingScalars.overcrowding_scalar theorem. No spectral or
probabilistic manuscript claim may be used as an assumption.
