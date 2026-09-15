# MF-24: statement-first numerical and general boundary

Status: proposed statements only. No proof implementation, Lean execution,
independent statement approval or frozen boundary is claimed by this file.
The complete canonical negative target is retained at upstream
`8f04b905eb2e0827b6b84f37d9d080ae1f05b202`. Mathematical proof credit is
**Georg Maierhofer, University of Cambridge**. Formalization credit is
**George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA**. No George
email is included.

## Exact target and data

Matrices are complex square matrices. Norms are norms of the associated
continuous linear maps on `EuclideanSpace ℂ (Fin N)`, hence genuine induced
Euclidean operator norms. Singular values are Mathlib's actual ordered singular
values of the corresponding Euclidean linear map, including multiplicities and
zeros. SIP means equality of all N such values after **every complex shift**.
Polynomial evaluation is `Polynomial.aeval` for arbitrary complex polynomials.

The final target is the negation of

`∃ C>0, ∀ N≥1, ∀ A B, SIP(A,B) → ∀ p∈ℂ[X], ‖p(A)‖₂≤C*‖p(B)‖₂`.

The stronger exported witness statement gives, for every real C≥0, an actual
finite member of the unchanged family with nonzero denominator and ratio
strictly greater than C. No real supremum with an unbounded-set default value
is used.

For every integer m≥2 and real t>1:

* k=m+1, D=m+2, N=k²=mD+1.
* U=(t,1,…,1) has length m.
* The source edge words are X=(U,1,U,(t⁻¹,U)^(m−1)) and
  Y=(U,(t⁻¹,U)^(m−1),1,U), each of length N−1.
* The actual matrices have entry w_r in row r and column r+1, and zero elsewhere.
  They are defined from the source words, without assuming a height identity.
* At vertex v=qk+s<N the heights are hX=1_{s≥1}+1_{q≥1} and
  hY=1_{s≥1}+1_{q=m}. A separate required theorem identifies the source shifts
  with their height-ratio matrices.
* The common complex polynomial is p_m=Σ_{j=1}^m X^(Dj), of degree N−1,
  with zero constant term. Actual matrix powers and actual polynomial
  evaluation, including every entry, must be related to the height formulas.

## Spectral equality without sampled shifts

For any finite real edge word w, complex shift z and scalar η∈ℂ, put
ρ=|z|² and u=ρ+η. The actual leading Gram-plus-ηI determinants satisfy
d₀=1, d₁=u and

`d_(j+1)=(u+w_j²)*d_j−ρ*w_j²*d_(j−1)`.

The full determinant equals the first coordinate of
K(w_(N−1)²)…K(w₁²)(u,1)ᵀ, where K(a)=[[u+a,−ρa],[1,0]]. Later edges
multiply on the left. No determinant expansion growing factorially with N
is an acceptable implementation plan.

For arbitrary complex 2×2 P and scalars u,ρ,a,b, set R=PK(a), S=PK(b),
v=P(u,1)ᵀ. Require the exact identity

`(R^n*S*v)_0=(S*R^n*v)_0` for every n≥0.

There is no invertibility or nonzero-parameter hypothesis. This is algebraic
matrix multiplication, not conjugate transpose. The proposed proof is an exact
compressed-commutator identity followed by actual 2×2 Cayley–Hamilton.

Apply it with P=K(1)^(m−1)K(t²), a=t⁻², b=1 and n=m−1. Equality of all
complex η determinant evaluations implies equality of the actual shifted Gram
characteristic polynomials. A required generic bridge then gives equality of
the actual complete singular-value lists. Characteristic-polynomial equality
must not silently replace the SIP definition.

## Exact norm obligations and computation reduction

The first row of p_m(X) has m nonzero entries t², so its squared Euclidean
norm is t⁴m and the induced operator norm is at least t²√m. The actual
polynomial p_m(Y) is nonzero; the source proves its (0,N−1) entry is t².

For each residue c modulo D, use **all** vertices v<N with v%D=c. These
finite classes partition the full vertex set. Each class contains at most
m+1 vertices, at most one Y-height zero and at most one Y-height two. All
other Y-heights are one. The two full-vector sums satisfy

`Σ t^(−2hY(v))≤1+m/t²`,  `Σ t^(2hY(v))≤t⁴+m*t²`.

Their product is (t²+m)². The polynomial matrix is zero between different
classes, and its nonnegative within-class entry is bounded by the full outer
product t^(−hY(r))*t^(hY(s)). Finite Cauchy–Schwarz and the partition must
therefore prove, for **every complex Euclidean vector** x,

`‖p_m(Y)x‖₂²≤(t²+m)²*‖x‖₂²`, hence `‖p_m(Y)‖₂≤t²+m`.

This deliberate bound is slightly weaker than the source's t²+m−1. It removes
zero-column/zero-row deletion and block permutation/isometry bookkeeping.
It preserves the full canonical negative target: the ratio is at least
√m/(1+m/t²), and at the finite rational choice t=m it is at least (2/3)√m.
For any C≥0, a natural m≥2 with m>(3C/2)² gives a ratio strictly above C.
No interval arithmetic, approximate SVD, discretized shift range, limit of
matrices or fixed finite list of dimensions is involved.

## Independent Challenge map

The proposed exports in `Challenge.lean` separately require:

1. `family_dimensions`: exact growing dimension and both word lengths.
2. `source_words_eq_height_shifts`: source/height bridge and all height bounds.
3. `height_shift_powers`: every actual power entry, including exponent zero.
4. `family_nilpotent_nonnegative`: both actual nilpotent real nonnegative matrices.
5. `polynomial_degree_evaluation`: exact degree, zero value and actual evaluation.
6. `polynomial_entries`: the full residue-supported entry formula.
7. `gram_continuant`: actual leading determinant recurrence and both base cases.
8. `gram_transfer`: full determinant and correctly ordered transfer product.
9. `transfer_bridge`: the arbitrary-parameter, all-power 2×2 identity.
10. `family_gram_charpoly`: equality at every complex shift.
11. `gram_singular_bridge`: complete actual ordered singular-value bridge.
12. `family_super_identical`: full canonical SIP for every family parameter.
13. `first_row_and_nonzero`: exact numerator row energy and nonzero denominator.
14. `polynomial_numerator_bound`: actual induced operator norm lower bound.
15. `residue_geometry`: unique full partition and the three cardinality bounds.
16. `residue_weight_bounds`: both exact full-vector sum bounds.
17. `polynomial_denominator_energy`: the bound for every complex Euclidean vector.
18. `polynomial_denominator_bound`: the actual induced operator norm upper bound.
19. `polynomial_norm_ratio`: the parameter-dependent lower bound.
20. `finite_rational_family_ratio`: the bound (2/3)√m at t=m.
21. `arbitrarily_large_ratios`: concrete family witnesses above every C≥0.
22. `no_uniform_comparison`: negation of the full original comparison assertion.

The source-sharper t²+m−1, the factor 4/5, padding to every dimension,
the stated bound on C_N and the liminf corollary are **not claimed** by these
statements. They are not needed to negate the original uniform bound; the
remaining quantitative questions are unchanged.

Before proof bodies: independent source/definition review by two other agents,
actual remote Linux statement typechecking and immutable statement hashes.
After implementation: all exports need LeanCert kernel trust, permitted-axiom
audit, Comparator without definition holes, default-kernel replay and negative
controls, two independent final referees, and truthful formalization metadata.
