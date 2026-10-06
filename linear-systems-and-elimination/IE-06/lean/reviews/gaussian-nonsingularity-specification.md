# Gaussian nonsingularity foundation: specification before implementation

2026-10-06. The complete probabilistic proof is now requested; the earlier
statement-only delivery is a completed historical phase, not the current goal.

The exact foundation proposed by the coordinator and independently approved
by the source-analysis agent before implementation is:

1. For every natural `d`, every family of atomless probability measures on
   `ℝ` indexed by `Fin d`, and every nonzero real multivariate polynomial in
   those variables, its evaluation is nonzero almost surely for their actual
   product measure. No absolute-continuity hypothesis is needed. Dimension zero
   is included and reduces to a nonzero constant polynomial.
2. Uncurrying the concrete nested Gaussian matrix law and reindexing by
   `finProdFinEquiv` gives exactly the flat product law on `Fin (n*n)` entries.
3. The determinant polynomial is nonzero, witnessed by evaluation at the
   identity matrix, including the empty identity with determinant one.
4. Therefore `gaussianMatrix n {A | A.det = 0} = 0` for every natural `n`,
   exactly the existing Challenge signature.

The reviewed argument uses induction on the number of polynomial variables,
Fubini, the finiteness of roots of a nonzero univariate polynomial, and
atomlessness. The local RRF formalization
`RRF/Proofs/SketchRank.lean`, lines 1–162, supplies reusable proof structure;
the adaptation must have standalone Mathlib/IE-06 imports and retain source
provenance. No RRF-specific proposition is imported or assumed. All adapted
declarations must pass fresh elaboration and transitive kernel-axiom checks.

This foundation proves no spectral tail, concentration inequality, or IE-06
growth estimate. Those remain separate obligations in the full proof.
