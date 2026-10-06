# Gaussian inverse principal Gram moments

Root independently approved this simplified unconditional route before code on
2026-10-06. It proves the exact unconditional moments required by the A3 Markov
argument, without an unnecessary separate law for every deterministic fiber.

For natural k,r,n,q with k+r+2q≤n, let G have k+r independent Gaussian rows,
and let tailRows r G be its last k rows (after deleting the first r rows).
Prove integrability and

`E[(detGram(tailRows r G)/detGram(G))^q] =
 ∏a∈range r ∏b∈range q (((n-k-a:ℕ):ℝ)-2(b+1))⁻¹`.

The column dimension minus the number of other rows is computed before casting.
All denominator factors are positive. r=0 has ratio1 almost everywhere because
Gram is nonsingular almost everywhere; q=0 has power0=1. These conventions are
retained in the implementation. Induct r by integrating the first row using
actual product Gaussian law, the proved cofactor/residual identity, and Fubini
with absolute integrability. No conditional distribution is assumed.

Then prove the deterministic Schur/Jacobi identity on full rank: determinant
of the first r principal block of inverse Gram is the above determinant ratio.
A fixed row permutation preserves the entire Gaussian law and transfers this
identity and moment to any fixed size-r principal subset. The final object is
an actual principal submatrix of the ordinary inverse Gram, interpreted almost
everywhere on the full-rank event. No surrogate determinant or weaker moment
bound is substituted.
