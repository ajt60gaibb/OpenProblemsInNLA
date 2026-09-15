# MF-24 independent full-source referee

Reviewer: `/root/next_inequalities`, 15 September 2026. This reviewer did not
write MF-24's definitions, Challenge, or proof modules. The mathematical source
is Georg Maierhofer, University of Cambridge. The formalization is by George
Stepaniants, Department of Computing and Mathematical Sciences, California
Institute of Technology; no George email is published.

**Source-level approval: no blocking mathematical or fidelity finding.** This
is not final verification or publication acceptance. The complete current
source still needs successful remote Lean elaboration, all 22 actual LeanCert
kernel assertions, permitted-axiom checks, independent Comparator without
definition holes, default-kernel replay, negative controls, and reconciliation
of the accepted bytes by two independent final referees. No local Lean/Lake or
dependency download was run for this review.

## Exact reviewed boundary

`INPUTS.json` binds the complete source snapshot retained under `source/`, the
canonical README and full proof.tex at upstream
`8f04b905eb2e0827b6b84f37d9d080ae1f05b202`, and all 22 export-to-module mappings.
All immutable files listed in STATEMENT-FREEZE.json match their frozen hashes.
Every exported signature text matches the independent frozen Challenge after
whitespace normalization. This textual check is a preflight; Comparator must
still check elaborated declarations and definitional alignment.

I read the entire canonical README and manuscript, Definitions, all 22
Challenge declarations, all 20 mathematical helper/proof modules, Solution,
NUMERICAL_TARGETS and SourceCorrespondence. The local import closure from
Solution includes all reviewed NLA modules and does not include Challenge.
The proof-source scan found no sorry/admit, custom axiom, unsafe or native proof
shortcut. These are source observations, not a transitive compiled axiom audit.

## Fidelity and mathematical route

1. The final target is the negation of a single positive comparison constant
   for every dimension N≥1, complex matrices A,B, and every complex polynomial.
   SIP retains every complex shift z and all N actual ordered singular values,
   including repeated and zero values. The norms are the norms of actual
   continuous linear maps on EuclideanSpace ℂ (Fin N), and polyEval is aeval.
   No sampled shift set, scalar norm substitute, or additional normality,
   invertibility, rank, or distinct-spectrum hypothesis enters the target.
2. The matrices remain defined by Maierhofer's actual edge words. Dimensions
   proves the exact N−1 lengths. Words and Heights separately establish the
   word-to-height identity at every edge. Powers proves all actual entries by
   induction with a single possible intermediate vertex, including exponent
   zero, truncated paths and zero dimension. Polynomial proves the actual
   evaluation, exact degree N−1 and full forward residue-supported entry rule.
3. Continuant's last-border determinant uses two Laplace expansions, including
   the empty minor, with no division or nonzero-minor requirement. GramEntries
   computes the actual conjugate-transpose Gram pencil. In particular, the two
   adjacent entries are −z*w and −conj(z)*w, whose product is |z|²*w². Its
   leading corners agree because the new bidiagonal row is zero in earlier
   columns. GramContinuant therefore concerns actual determinants, for all
   complex z and η, rather than an independently defined recurrence proxy.
4. Transfer multiplies each new edge on the left, exactly matching the reverse
   order in transferProduct. Bridge proves the compressed 2×2 commutator and
   reduces arbitrary powers to the span of I,R by Cayley–Hamilton, including
   singular parameters. It does not assume the transfer matrices commute.
   FamilyTransfer matches the two unchanged edge-word products. FamilySpectrum
   passes from every complex η determinant evaluation to actual Gram charpoly
   equality. SpectralBridge then uses actual adjoint-composition eigenvalues,
   the complete finite-dimensional eigenvalue equality theorem, and the actual
   singularValues_fin definition. This retains all multiplicities and zeros.
5. Numerator counts exactly the m positive multiples of D in the first row,
   each entry t², giving energy m*t⁴. Its denominator nonzero proof uses the
   actual (0,N−1) polynomial entry t². NormBasics uses the adjoint acting on a
   unit coordinate vector for the row lower bound and the universal CLM energy
   criterion for the upper bound; these are actual induced Euclidean norms.
6. Geometry partitions every vertex by its residue modulo D. Within each full
   class it proves cardinality≤m+1, at most one height-zero vertex, and at most
   one height-two vertex, using exact congruences and injectivity. Weights bounds
   the two full sums by 1+m/t² and t⁴+m*t². Energy retains every complex input
   vector, uses the complex triangle inequality and real finite Cauchy–Schwarz,
   and sums over the exact partition. The resulting energy bound is
   (t²+m)²*||x||², with nonnegative multipliers checked throughout.
7. The deliberate denominator bound t²+m is weaker than the manuscript's
   t²+m−1, but it is sufficient for the complete canonical negative answer.
   With t=m the ratio is at least (2/3)*sqrt(m). Ratios supplies an explicit
   finite natural witness above (3*(C+1))²+2 for each C≥0; Unbounded combines it
   with genuine SIP and contradicts the full uniform comparison. No limit,
   unbounded-set supremum convention, or finite testing inference is used.
   The source's sharper 4/5 constant, padding to every dimension, and precise
   asymptotic quantitative corollaries are explicitly unclaimed and remain so.

## Independent exact diagnostics and proof efficiency

`independent_checks.py` is retained and reproducible using only Python's
standard library. Its eight-variable polynomial arithmetic independently
checks the compressed commutator as the zero polynomial and all four generic
2×2 Cayley–Hamilton entries. Exact rational diagnostics check 57 family
parameters, 19,722 source edges, all 741 full residue classes in those cases,
17,510 actual full polynomial entries in modest complete dimensions, numerator
energy, denominator nonvanishing and transfer equality. CHECKS.json records
the outcomes. The finite cases are supplementary, and are not used as a
universal proof certificate, floating-point SVD, or substitute for the source
proof of the complex-vector energy inequality.

The implementation is appropriately reduced: dimension-dependent algebra is
proved by generic induction, sparse paths and finite-sum inequalities. Only
fixed 2×2 polynomial algebra is expanded. No interval subdivision or growing
factorial determinant computation is needed. LeanCert kernel trust is the
appropriate use here because every obligation is exact algebra or analysis.

## Remaining acceptance work

The current metadata intentionally still describes its original statement
stage. Before publication, update README/formalization.yaml to the actual
accepted implementation and run status, without changing immutable numerical
or Challenge bytes. In particular, do not treat the current source approval
or finite exact diagnostics as a completed Lean proof. Reconcile all accepted
source hashes, complete raw kernel/Comparator/control receipts, and canonical
path/credit/duplicate checks before adding a verified count or upstream PR.
This applies the project's scoped Tau Ceti fidelity, proof quality, reuse and
attribution standards; it is not official Tau Ceti or human peer endorsement.
