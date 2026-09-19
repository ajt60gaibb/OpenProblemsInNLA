# Supplemental mathematical feasibility notes

These are reviewer-derived proof plans, not Lean proof implementations, new-resolution claims, or independently approved replacements for the frozen packet. The approval in REVIEW.md concerns the original mathematical contracts. If either plan is adopted, spell out and independently review its concrete helper statements before implementation. All matrices below are finite-dimensional complex matrices; traces of Hermitian expressions are real.

## C16 without differentiating eigenvectors or a noncommuting logarithm

For Hermitian X,Y whose spectra lie in a fixed compact interval J ⊂ (0,∞), diagonalize them separately and write λ_i, μ_j for their eigenvalues. Let p_ij be the squared modulus of the overlap between their orthonormal eigenvectors. Then p_ij ≥ 0 and both marginals sum to one. For f(x) = −x log x and L ≥ sup_J |f''|, scalar Taylor's theorem gives

`|f(μ)−f(λ)−f'(λ)(μ−λ)| ≤ (L/2)(μ−λ)^2`.

The spectral trace and overlap identities imply

`|tr f(Y)−tr f(X)−tr(f'(X)(Y−X))|`
`  ≤ (L/2) Σᵢⱼ pᵢⱼ(μⱼ−λᵢ)^2`
`  = (L/2) tr((Y−X)^2)`
`  ≤ (L n/2) ||Y−X||op^2`.

The middle equality expands into tr Y² + tr X² − 2 tr XY, so it makes no eigenvector-continuity or spectral-multiplicity assumption. A small operator-norm neighborhood of any X > 0 has spectra in such a J by Loewner bounds. This proves the trace derivative `D(tr f)(X)[E] = tr(f'(X)E)` with a quadratic remainder. Apply it to X = A+B and Y = A+U_tBU_t*, use Y−X = t·i[H,B]+o(t), and cancel tr(i[H,B]) = 0. The requested C16 follows with f'(X) = −log X−I. This route can reuse the already proposed MI24 overlap algebra; it does not need a general derivative theorem for CFC.log.

## A possible C11 route using layer cake and inertia

This route still requires substantial internal lemmas. It may avoid the residue theorem, generic simple-spectrum pencils, and continuity extension in the paper's proof. It is an audit derivation, not a claim that the necessary complex-Hermitian inertia interface already exists in Mathlib.

Write Δ = σ−ρ, A(t) = ρ+tΔ, and w(t) = 1/(|t|(t−1)²), disregarding t = 0,1 or assigning arbitrary integrand values there. Let ν₋(Z) count strictly negative eigenvalues with multiplicity. Spectral layer cake gives

`tr A(t)₋ = ∫₀∞ ν₋(A(t)+rI) dr`.

For fixed r ≥ 0, put P = ρ+rI > 0 and C_r = P^(-1/2) Δ P^(-1/2). Congruence gives

`ν₋(A(t)+rI) = ν₋(I+tC_r)`.

Every eigenvalue c of C_r exceeds −1, since I+C_r is congruent to σ+rI > 0. Thus the negative-eigenvalue counting function is the finite sum of indicators of 1+tc < 0. Direct scalar integration gives, for every c > −1,

`∫ℝ w(t) · 1_{1+tc<0} dt = log(1+c) − c/(1+c)`.

For c > 0 the interval is (−∞,−1/c); for −1 < c < 0 it is (−1/c,∞); for c = 0 it is empty. A primitive of 1/[t(t−1)²] is log|t|−log|t−1|−1/(t−1). This checks both signs and the zero endpoint explicitly.

Tonelli applies to the nonnegative measurable layer-cake integrand. Therefore the pencil integral becomes ∫₀∞ Φ(r) dr, where

`Φ(r) = tr log(I+C_r) − tr(C_r(I+C_r)^(-1))`
`     = log det(σ+rI) − log det(ρ+rI) − tr(Δ(σ+rI)^(-1))`.

Here determinants are positive real numbers under their canonical identification. The logarithmic determinant identity uses determinant multiplicativity under the congruence; the second term uses ordinary trace cyclicity. Neither claims similarity of A(t)+rI and I+tC_r: congruence preserves inertia, not eigenvalues or trace.

Let F(r) = tr((ρ+rI)(log(ρ+rI)−log(σ+rI))). Differentiation along identity shifts, in the fixed individual eigenbases of ρ and σ, gives F'(r) = −Φ(r). This is the identity-shift calculation in [Frenkel's Lemma 5](https://arxiv.org/html/2208.12194v4); the general C16 derivative is not required. Scalar logarithm asymptotics give lim_{r→∞} F(r) = tr(ρ−σ) = 0. Thus the pencil integral equals F(0) = D(ρ||σ). The explicit t-to-γ substitutions and two-sided cutoff then give C11.

Outstanding internal prerequisites are the spectral counting/layer-cake measurability and Tonelli step, complex-Hermitian inertia under invertible congruence, the scalar improper integrals and tail limit, trace-log/determinant compatibility, and the identity-shift derivative. The pinned library search found real quadratic-form signature machinery, including `QuadraticMap.Equivalent.sigNeg_eq`, but no directly matching complex-Hermitian matrix inertia result. A bridge or a direct finite-dimensional negative-subspace argument must be proved, not assumed. This approach handles repeated eigenvalues directly; it does not establish that the formalization is small or already available.
