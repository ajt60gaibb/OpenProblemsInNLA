# IS-03 proof map

The seven independently reviewed statements are unchanged. This file explains the
implementation of Matthew J. Colbrook's counterexample, formalized by George
Stepaniants, Department of Computing and Mathematical Sciences, California
Institute of Technology, Pasadena, California, USA. The work is AI-assisted.

`Algebra.lean` proves preservation of entrywise nonnegativity under every natural
matrix power using `Matrix.pow_apply_nonneg`; summing the diagonal proves trace
nonnegativity, including order zero and exponent zero. It checks the unchanged
witness's entries and trace. Its explicit integer Bézout identity for `7q` uses
coefficients of at most 22 bits and proves that the actual derivative polynomial
`q` is separable. Monicity and exact degree six are proved separately.

`Witness.lean` reindexes the actual seven-by-seven matrix as a three-plus-four
block matrix. The characteristic-polynomial product theorem reduces the
calculation to actual determinants of orders three and four. No seven-by-seven
permutation enumeration is performed. Polynomial differentiation then proves
that the actual normalized derivative is the frozen polynomial `q`.

`Spectral.lean` supplies the arbitrary-real-matrix bridge. Separability and
algebraic closedness give six distinct complex roots. For an arbitrary real
matrix `B` with characteristic polynomial `q`, the actual complexified linear
map has a nonzero eigenvector at every root. Distinct eigenvalues give linear
independence. Equality of cardinality and dimension produces a basis. Thus
diagonalizability is **derived**, never assumed. Actual basis matrices identify
both the complete characteristic-factor product and the trace of every natural
matrix power. Ring-homomorphism and trace lemmas connect these calculations back
to the original real matrix, without symmetry or nonnegativity assumptions.

`Newton.lean` evaluates Mathlib's genuine multivariate Newton identity at an
arbitrary finite family of six complex values. Vieta's formula identifies all
elementary symmetric functions from the full polynomial product. The seven
finite recurrences prove exactly the frozen moments, retaining multiplicity;
the helper needs no distinctness assumption. This bounded module was implemented
by the coordinator after the statement gate, in parallel with the matrix bridge.

`Numerical.lean` uses LeanCert's explicitly selected kernel mode for the sole
scalar sign `(-8593 / 823543 : ℝ) < 0`. This is a singleton rational certificate,
with no interval search or broad enclosure. The certificate is consumed by
`negative_moment_proved`, then the nonnegative-trace contradiction, and finally
the complete universal conjecture's negation.

`Proof.lean` combines the genuine matrix traces and Newton sums, then instantiates
the seventh moment. `Solution.lean` exports all seven exact Challenge signatures.
The universal target is refuted by its order-seven instance. No zero padding,
restricted class of realizing matrices, spectral assumption, or companion-only
surrogate replaces the original target. The finite Python diagnostic remains
supplementary and is not used by Lean.

Historical statement-stage documents and their recorded obligations remain
unchanged. Final local checks, independent proof review, and actual Linux
Comparator verification have separate receipts; none is inferred from another.
