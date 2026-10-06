# Gaussian operator inverse moment specification

Root independently approved this exact contract before implementation on
2026-10-06. This extends the frozen exact GaussianRegression directional moment.

For m≥1, a real positive semidefinite matrix H of size m, and natural q,
put D_q = ∏j∈range q (1+2j). Prove integrability and

`D_q * Spectral.opNorm H ^ q ≤ ∫z~stdGaussian(R^m) (zᵀHz)^q`.

All operator norms are the genuine Euclidean induced norm. The proof uses
an eigenvector attaining the largest eigenvalue, positivity of the remaining
spectral terms, and actual Gaussian rotational invariance. Upper domination
by opNorm(H)^q times ‖z‖^(2q) proves integrability first.

For m≥1 and n≥m+2q, literal iid standard Gaussian G under gaussianRect m n,
and W=G Gᵀ, prove integrability and

`E[opNorm(W⁻¹)^q] ≤ (∏j<q(m+2j)) / (D_q * ∏j<q(n-m+1-2(j+1)))`.

Natural subtraction occurs before casting dimensions to real. Denominator
factors are strictly positive under the dimension hypothesis. q=0 uses the
empty product and 0^0 conventions. Use the actual jointly measurable
quadratic integrand, the proved directional moment, and Fubini; no conditional
probability theorem is assumed.

Finally for 1≤r, m≤r, 3r≤n, x>0 prove

`P[opNorm(Spectral.pinv G)^2 > 3*exp(2+x/r)/r] ≤ exp(-x)`.

The spectral pseudoinverse is genuine, including singular matrices; its
full-rank Gram identity applies almost everywhere by the proved rank law.
Handle m=0 separately. The bound has the required inverse-r scaling. The
universal constant 3 replaces the manuscript's 2, as independently approved
by root because subsequent targets quantify an unspecified universal constant;
the exponential x/r is stronger than the source 2x/r. No weakening by replacing
the operator norm with Frobenius norm is allowed.
