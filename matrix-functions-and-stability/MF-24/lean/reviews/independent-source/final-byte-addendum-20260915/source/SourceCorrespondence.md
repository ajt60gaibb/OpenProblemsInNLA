# MF-24 source correspondence — proposed boundary

This is a statement-only draft for the complete negative resolution of MF-24.
No Lean proof, independently approved boundary, remote typecheck or verified
status is claimed. The canonical source and complete retained manuscript were
read at upstream `8f04b905eb2e0827b6b84f37d9d080ae1f05b202`; exact source
hashes and primary Mathlib source inspection are recorded in
`SOURCE-PROVENANCE.json`.

The original mathematical counterexample is due to **Georg Maierhofer,
University of Cambridge**. **George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology, Pasadena, California,
USA**, is the formalization author. These are different people and different
credits. No George email is published.

## Canonical target

The retained canonical page asks whether one constant compares all complex
polynomial operator norms for every dimension and every pair whose complete
singular-value lists agree after every complex shift. `UniformComparison`
states exactly that assertion with an arbitrary positive real constant and all
positive natural dimensions. Restricting the constant to be positive loses no
candidate uniform bound. `no_uniform_comparison` negates the assertion, and
`arbitrarily_large_ratios` requires explicit family witnesses with nonzero
denominator for every nonnegative real bound.

`spectralNorm` explicitly uses the norm of `Matrix.toEuclideanCLM`, whose
domain and codomain are Euclidean spaces. `singularValue` uses
`LinearMap.singularValues` of `Matrix.toEuclideanLin`. Its zero-based `Fin N`
indices contain every ordered singular value, with multiplicities and zeros.
`SuperIdentical` quantifies the complete complex plane. `polyEval` is actual
`Polynomial.aeval` in complex matrices. None of these semantic objects is
replaced by a characteristic-polynomial test, a finite shift sample, a custom
entry proxy or a different matrix norm.

## Proposed statement map

Every declaration in the following table currently exists only as a goal in
the independent `Challenge.lean`; no implementation is present. The Challenge
may use deliberate placeholders and must never be imported by the future
Solution environment. `comparator.json` requires all 22 declarations, with no
definition holes and only the three standard permitted Lean axioms.

| Challenge declaration | Retained manuscript argument | Required scope |
| --- | --- | --- |
| `family_dimensions` | Construction in Section 1 | Every m≥2; N=(m+1)²=m(m+2)+1 and both complete edge lengths |
| `source_words_eq_height_shifts` | Prefix-height equations in Section 3 | Both source words and every actual vertex; initial heights and full height range |
| `height_shift_powers` | Unique weighted path formula | Arbitrary height function, positive t, all powers including zero, all finite indices |
| `family_nilpotent_nonnegative` | Source construction | Actual Nth powers zero and every entry real nonnegative |
| `polynomial_degree_evaluation` | Common polynomial and degree | Zero constant term, exact degree N−1, actual evaluation at every matrix |
| `polynomial_entries` | Residue-block entry formula | Every entry and every forward residue separation; no missing superdiagonal |
| `gram_continuant` | Tridiagonal determinant recurrence | Actual leading determinants, both base cases and every valid prefix length |
| `gram_transfer` | Ordered transfer product | Actual complete determinant; later edges multiply on the left |
| `transfer_bridge` | Lemma 2 | Every complex P,u,ρ,a,b and n; no inverse, excluded parameter or conjugate transpose |
| `family_gram_charpoly` | End of Section 2 | Actual Gram characteristic polynomials at every complex shift |
| `gram_singular_bridge` | Hermitian-spectrum argument | All ordered singular values, retaining multiplicities, zeros and repeated roots |
| `family_super_identical` | Theorem 1 spectral claim | Full original SIP definition for every m≥2 and t>1 |
| `first_row_and_nonzero` | Numerator and nonzero-denominator paragraph | Exact row energy t⁴m and actual nonzero polynomial denominator matrix |
| `polynomial_numerator_bound` | Theorem 1 first inequality | Genuine operator norm at least t²√m |
| `residue_geometry` | Residue-block paragraph | Full unique partition; class size ≤m+1; at most one height zero and one height two |
| `residue_weight_bounds` | Adaptation of the source outer-product estimate | All class vertices retained; both exact real sums bounded |
| `polynomial_denominator_energy` | Finite Cauchy–Schwarz argument | Every complex Euclidean input vector; bound (t²+m)² |
| `polynomial_denominator_bound` | Adaptation of Theorem 1 second inequality | Actual induced norm at most t²+m |
| `polynomial_norm_ratio` | Adaptation of Theorem 1 ratio | Every m≥2 and t>1; actual nonzero denominator |
| `finite_rational_family_ratio` | Adaptation of Section 4 finite choice | Unchanged t=m family; lower bound (2/3)√m |
| `arbitrarily_large_ratios` | Finite-family divergence | A finite valid member above every prescribed real C≥0 |
| `no_uniform_comparison` | Complete original admission target | No constant works for all dimensions, SIP pairs and complex polynomials |

## Explicit proof simplifications and unclaimed statements

The transfer argument is planned over scalar ℂ for every η rather than over
the ring of complex polynomials in η. Equality of all determinant evaluations
still implies equality of the actual characteristic polynomials over the
infinite field ℂ. The Gram-plus-ηI to characteristic-polynomial sign change
must be proved, not assumed. Mathlib's Hermitian spectrum and singular-value
definitions provide the genuine spectral-list bridge.

The norm proof deliberately retains every coordinate of every residue class.
The complete nonnegative outer-product majorant gives t²+m instead of the
source's sharper t²+m−1. At t=m this yields (2/3)√m, which diverges and
fully refutes the same canonical dimension-independent assertion. Both
independent statement referees must approve this explicitly documented
quantitative simplification. No interval splitting, numerical SVD or fixed
sample of dimensions is an implementation substitute.

The sharper factor 4/5, the all-dimension padding corollary, the manuscript's
specific lower bound for C_N and its liminf assertion are outside this proposed
formal boundary. The exact dimension-dependent constants and their optimal
growth remain open, as stated by the canonical page. No claim about those
additional targets is made.

## Review and mechanical gates

The statement draft follows the independently checked Challenge/Solution and
trust organization studied in the pinned Schiffer and Forsythe examples.
Before implementation, two other agents must review these actual definitions,
quantifiers, numerical targets and source correspondence; actual Linux
statement elaboration must pass; then their hashes are frozen. No reviewer
approval is inferred from the author's assessment.

The eventual proof must use exact algebra and generic finite recurrences,
reuse the available Mathlib spectrum APIs, and include LeanCert kernel trust
assertions on every export. Final acceptance additionally requires the actual
Compiler and Comparator receipts, a transitive permitted-axiom audit,
default-kernel replay, negative controls and two independent final referees
applying the scoped Tau Ceti fidelity, proof quality, reuse and attribution
standards. No official Tau Ceti endorsement is implied. All these gates are
pending for MF-24.
