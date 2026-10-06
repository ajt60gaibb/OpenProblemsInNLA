# Gaussian negative Gram determinant moments

Root independently approved this exact mathematical statement before code on
2026-10-06. Ownership: GaussianDeterminantMoments.lean, separate from the frozen
Gaussian regression, operator inverse, radial moment, and spectral modules.

For natural m,n,q with m+2q≤n, literal iid standard Gaussian G under
GaussianNull.gaussianRect m n, and gram(G)=G Gᵀ, prove integrability and

`∫ ((det(gram G))^q)⁻¹ = ∏a∈range m ∏b∈range q (((n-a:ℕ):ℝ)-2(b+1))⁻¹`.

Each factor is strictly positive under the hypothesis. Empty-row matrices
have determinant 1, and q=0 gives integrand 1 and empty inner products.
Ordinary determinant powers use their usual totalized scalar inverse; the
singular exceptional set is null by the proved Gaussian full-row-rank law.

Induct on m. For fixed remaining full-rank rows B and a fresh first row y,
the inverse Gram cofactor formula gives invGram00 = detGramB / detGram(cons y B).
The already-proved exact residual identity gives invGram00 = ‖projection(y)‖⁻².
Raise to q and apply the proved residual inverse radial moment, then Fubini
with the actual product Gaussian law and absolute integrability. No Bartlett
independence assertion is assumed. Conditional inverse principal block moments
are a separate subsequent contract.
