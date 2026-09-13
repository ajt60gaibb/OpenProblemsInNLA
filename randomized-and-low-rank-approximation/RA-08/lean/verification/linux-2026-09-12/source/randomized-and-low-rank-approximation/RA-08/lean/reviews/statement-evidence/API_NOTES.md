# Actual pinned API and scope inspection

The statement-only inspector prints the actual compiled definitions and instance
arguments rather than relying on theorem names. `API-SOURCE-INPUTS.json` binds
the inspected source files to their real Git commits and blob identities;
`RUBRIC-INPUTS.json` matches all twelve retained rubric Markdown files to the
campaign manifest at TauCetiReview `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`.

- `Mathlib/Analysis/CStarAlgebra/Matrix.lean`: `Matrix.toEuclideanCLM` is a star
  algebra equivalence to continuous linear endomorphisms of real Euclidean
  space. The definition supplies `(n := Fin n) (𝕜 := ℝ)` explicitly. Its norm
  is the CLM operator norm. `l2_opNorm_toEuclideanCLM` and
  `l2_opNorm_diagonal` provide exact L2 matrix-norm bridges when the correct
  scoped instances are active. The default matrix norm is not used in the
  target. The initial missing explicit parameters caused an elaboration error,
  not a successfully compiled wrong norm; the original source/log is retained.
- `Mathlib/Analysis/Matrix/Order.lean`: scoped `MatrixOrder` defines `A≤B` as
  `(B-A).PosSemidef`; this is printed in the inspector. Real PSD means symmetry
  and nonnegative real quadratic forms. It is not an entrywise inequality.
- `Mathlib/Analysis/Matrix/Spectrum.lean`: `eigenvalues₀` is actually antitone.
  The general-index `eigenvalues` is a reindexing, so its index order must not
  be assumed. The complete arbitrary-Q structure does not hard-code either
  choice. Ordered existence and its tie cases are an explicit Challenge
  obligation; `eigenvectorUnitary` and `spectral_theorem` are available for
  its genuine library bridge.
- `Mathlib/LinearAlgebra/UnitaryGroup.lean`: real unitary matrices use the
  actual conjugate transpose, equal to transpose over the reals. The target
  structure reconstructs the actual matrix, and its semantics export must
  prove column orthonormality and eigenvector equations. Arbitrary signs and
  rotations in repeated eigenspaces are included by universal quantification.
- `Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean`: the genuine real
  CFC exists for real Hermitian matrices; every scalar function is continuous
  on their finite spectrum. The proposed all-selected-bases CFC theorem must
  relate the library's preferred spectral representation to each arbitrary
  Q, rather than defining the result by an unrelated chosen truncation.
- `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean`:
  `cfc_polynomial` identifies real polynomial evaluation with actual CFC;
  `cfc_mono` requires scalar order on the SAME matrix's spectrum and actual
  continuity there. It is not a theorem asserting that a scalar monotone
  function preserves order between different matrices. The kink minorant
  route must prove the spectrum and invoke this same-matrix theorem.
- `Mathlib/Analysis/Convex/Function.lean`: `ConcaveOn` is the usual all-pairs,
  all-nonnegative-weights convex-combination predicate. The other three actual
  predicates in `AdmissibleFunction` retain continuity, monotonicity and
  nonnegativity precisely on the half-line, with no generic value-zero
  assumption. These definitions and their instances are printed explicitly.
- LeanCert's actual `Tactic/Verification.lean` supplies the six definition-only
  `#assert_trust kernel` checks. Its `Tactic/IntervalAuto/PointIneq.lean` is the
  minimal planned import for the one positive rational singleton certificate.
  The IS-03 numerical module is an existing campaign example of explicit
  `set_option leancert.trust "kernel"` and `interval_decide (trust := kernel)`.
  No RA-08 interval or proof command has been written or run yet.

The successful author run has three commands, six kernel assertions on
DEFINITIONS and six printed standard-three axiom reports on those definitions.
All fourteen Challenge warnings are intentional. An earlier diagnostic parser
expected apostrophes rather than Lean's backticks around `sorry`; its exact
correction is retained. Neither issue changed mathematical scope after the
successful source typecheck.

The source witness, eigenvalue-count argument, scalar inequality, exact CFC
minorant and norm contradiction still require proofs. API availability and
rational diagnostics are not substitutes. The completion-only metadata checker
and authoritative Linux controls are not run at this statement-only phase.
