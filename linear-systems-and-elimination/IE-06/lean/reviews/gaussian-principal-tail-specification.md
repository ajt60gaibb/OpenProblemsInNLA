# Gaussian inverse principal-minor union tail

Root independently approved this exact contract before implementation on
2026-10-06. For naturals m,n,r,q with q>0, r≤m, m+2q≤n, and a>0, let
D_S(G)=det(((G Gᵀ)⁻¹).submatrix Subtype.val Subtype.val), where S is a literal
finite subset of Fin m. Prove

`P[∃S∈univ.powersetCard r, a≤D_S(G)] ≤
 ENNReal.ofReal((m.choose r)*(exp 1/q)^(r*q)/a^q)`.

This uses actual GaussianPrincipalMoments.gaussian_principal_subset_moment,
the proved inverse radial denominator bound for each of r factors, Markov's
inequality applied to D_S^q, and the exact finite powerset-cardinality formula.
Inverse Gram is positive semidefinite even at singular matrices, so the
principal determinants are nonnegative everywhere. No matrix spectral event
inclusion is assumed as a premise of this generic union estimate; the separate
spectral module will subsequently supply the deterministic implication.
The r=0 and all allowed dimension boundary cases remain included.
