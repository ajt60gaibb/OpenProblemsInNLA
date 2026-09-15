# MF-24 independent statement review

Reviewer: `/root`, an AI agent acting independently of the MF-24 author.
Phase: statement and numerical boundary review; 15 September 2026.
Verdict: **approve the mathematical statements at the attached hashes**.
Actual remote Linux elaboration remains required before freezing or writing proofs.
No complete Lean verification or Comparator acceptance is asserted here.

I read the canonical MF-24 README and complete Maierhofer counterexample manuscript
at upstream `8f04b905eb2e0827b6b84f37d9d080ae1f05b202`, then all Definitions,
22 Challenge signatures, numerical obligations and source correspondence. I also
inspected the pinned Mathlib definitions of `LinearMap.singularValues`,
`singularValues_fin`, `Matrix.toEuclideanCLM`, its Euclidean linear-map coercion
and matrix-vector action, and `Polynomial.aeval_def`. This is scoped Tau Ceti
fidelity, correctness, vacuity, generality, reuse and attribution review, not an
official Tau Ceti service run or human peer review.

## Target and definitions

`UniformComparison` is the full original uniform bound: every positive finite
dimension, arbitrary complex matrices and polynomials, and equality of every
actual ordered singular value after every complex shift. Requiring the constant
to be positive loses no possible finite bound. Its negation is backed by an
explicit family exceeding every nonnegative constant with nonzero denominator;
there is no unbounded-real-supremum default-value trap. The spectral norm is the
norm of the actual continuous linear operator on complex Euclidean space, not
the default entrywise matrix norm. Singular values preserve all N multiplicities
and zero values, with Mathlib's zero-based indexing explicitly converted from
`Fin N`. Matrix polynomials use the actual algebra homomorphism evaluation.

The source matrices remain word-defined. Their height representation is a
required theorem, so no desired matrix equality is hidden in a definition. Word
lengths, nilpotence, nonnegative real entries, all power entries including zero
exponent, and exact polynomial degree/evaluation are separate obligations.
The zero-dimensional case in the generic power lemma is harmless (there are no
indices), while the canonical dimension has an explicit positive lower bound.

## Spectral and numerical checks

The generic leading determinant uses the truncated upper shift's actual Gram
matrix. Its first diagonal is |z|²+η and subsequent diagonals include the previous
edge square; the off-diagonal product is |z|² times that square. Thus the proposed
continuant has the correct index j−1 and sign. The empty determinant is Lean's
ordinary 0-by-0 determinant. Reversing the list in the transfer product is the
correct order, since later edges act on the left. The bridge identity is valid
for arbitrary P: writing R=v fᵀ+a w gᵀ and S=v fᵀ+b w gᵀ makes the compressed
commutator zero; 2-by-2 Cayley-Hamilton reduces every power to R and I without
inverting any parameter. Charpoly equality is explicitly bridged to actual
ordered singular values; it is not substituted for the SIP definition.

Every forward same-residue separation is a polynomial exponent because
N=m(m+2)+1. The first row has m entries t². The full residue classes contain at
most m+1 vertices and at most one height 0 and one height 2. For t>1, the two
full-coordinate weight sums are bounded by 1+m/t² and t⁴+mt². Their product is
(t²+m)²; finite complex Cauchy-Schwarz and the full partition yield the stated
all-vector operator bound. At t=m≥2 the scalar denominator is 1+1/m≤3/2, so
(2/3)√m tends past every constant. These analytic observations validate the
intended statements, not an unimplemented proof.

## Scope, quality and remaining gates

The relaxed bound t²+m is deliberate, explicitly recorded, and sufficient to
settle the entire canonical uniform-boundedness target. The source's sharper
t²+m−1, factor4/5, padding bounds at every dimension and asymptotic corollary are
not claimed as formalized. Those related quantitative results remain unchanged.
The exact transfer and residue arguments avoid floating-point SVD, sampling of
complex shifts, interval grids, dimension-specific enumeration and factorial
large determinant expansion. Original mathematics stays credited to Georg
Maierhofer (University of Cambridge); George Stepaniants receives formalization
credit with Caltech department affiliation and no email.

The current Challenge contains22 deliberate placeholders in an independent
contract environment; Definitions contains no proof holes and no Solution exists.
Before proof bodies, obtain the other independent statement approval and an
actual successful Linux typecheck, then freeze the exact boundary. After proofs,
require all22 exports, LeanCert kernel assertions, standard transitive axioms,
fresh Comparator/default-kernel replay and rejection controls, and two final
independent reviewers on actual accepted bytes and logs. Syntax-only repairs
must be reviewed and rehashed before freezing.
