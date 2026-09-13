# IS-03 source-to-statement correspondence

This document records the statement boundary before proof. It does not assert
that any target in `Challenge.lean` is proved. All original documents are bound
by `source-inputs.json` to repository revision
`f41f1f9ffa2171550d4bb795862c6170c4f26070`.

## Sources and attribution

The complete canonical problem statement, authored `solution.md`, generated
`solution.tex`, original reviewed `IS-03.md`, independent informal review,
submission history and original-manuscript preservation note were read. The
IS-03 section of the supplied diagnostic was inspected as a diagnostic. Its
other problem-specific checks are outside this package. PDF rendering and a
new external literature or priority audit were not performed in this stage.

The original reviewed manuscript's complete-file SHA-256 is
`548553e2f177da2a2c5135030c6a34fff761d2b9c800b246b7f9a6797e02d45c`.
The source review and proof-hash manifest describe the metadata and
bibliographic changes between that draft and the authored manuscript. The
formalization retains Matthew J. Colbrook's counterexample and Johnson's
conjecture attribution. George Stepaniants receives formalization credit,
with the Department of Computing and Mathematical Sciences, California
Institute of Technology, Pasadena, California, USA. No George email is added.

| Original source location | Lean representation or obligation |
| --- | --- |
| Canonical “Problem statement,” every `n ≥ 5`, real nonnegative `A`, exact order `n−1` realization | `DerivativeRealizabilityConjecture` and final `not_derivativeRealizabilityConjecture`. `Fin n` provides labeled indices; natural subtraction is used only where `n ≥ 5`. |
| Canonical `p_A(z) = det(zI − A)` and polynomial equality | `Matrix.charpoly`, defined by `Matrix.det (Matrix.charmatrix A)`, and equality in `ℝ[X]`. Neither `p` nor `q` replaces the genuine characteristic polynomial by definition. |
| Source equation (1), exact `diag(1/2,C₂,C₄)` | `witnessMatrix`; its 49 real entries are unchanged. `witness_admissible` proves entrywise nonnegativity and genuine trace `1/2`. |
| Source equation (2), factored and expanded characteristic polynomial | `witnessPolynomial` is the proposed polynomial; `witness_polynomials` requires its equality to the actual matrix characteristic polynomial. |
| Source equation (3), `q = p′/7` | `normalizedDerivative` uses real reciprocal scalar multiplication of `Polynomial.derivative`. `derivativePolynomial` is a separate explicit polynomial; genuine equality, monicity and degree six are theorem conclusions. |
| Source equations (4)–(5), Newton identities and first six moments | `trace_moment_certificate` has arbitrary `B : RealMatrix 6` with the sole assumption `B.charpoly = derivativePolynomial`. Every trace value is a conclusion. |
| Source equations (6)–(7), seventh moment | Index `6 : Fin 7` denotes the seventh moment. The power in the trace contract is `i.val + 1`. `negative_moment` requires both exact value and strict negativity. |
| Theorem 1 proof, nonnegative powers have nonnegative trace | Generic `nonnegative_power_trace` includes all real square matrix orders and every natural power, even the harmless order-zero and power-zero cases. |
| Theorem 1, no nonnegative order-six realization; final canonical conclusion | `counterexample` states no such `B` for the actual derivative of the actual witness. `not_derivativeRealizabilityConjecture` negates the full quantified canonical claim. |

## Semantic points that independent referees must retain

`EntrywiseNonnegative` means `∀ i j, 0 ≤ A i j` in the real order. It is
not positive-semidefinite order. The trace is the genuine finite sum of
diagonal entries; `A ^ k` elaborates through `Matrix.semiring`, so it is
matrix multiplication, not entrywise powers. The characteristic polynomial
uses `X I − A`, not `A − X I`.

No diagonalizability, normality, Hermitian condition, invertibility, simple
roots, irreducibility or trace restriction is added. In the trace-moment
contract even nonnegativity is not assumed: all real realizations with that
characteristic polynomial must satisfy the identities. If the implementation
uses complex roots, it must prove the transport and the trace-power identity
with algebraic multiplicities. Mathlib's set of eigenvalues alone cannot
replace the characteristic-polynomial root multiset. If a property such as
separability is useful, it must be proved from the concrete polynomial.

The source's stronger no-zero-padding claim, Monov moment-conjecture
consequence, smallest-order question and historical novelty are not exported.
They are unnecessary to negate the complete exact-order canonical target.

## Independent author diagnostics and proof boundary

`reconstruct_exact.py` parses the frozen-to-be Lean matrix, polynomial and
moment literals, rather than importing the supplied diagnostic. A sparse
determinant expansion has only four supported permutations for the witness.
It proves the finite diagnostic equality of the parsed `p` to that determinant,
then differentiates exactly to get `q`. Newton recurrence and independent
companion-matrix powers reproduce all seven moments. Companion characteristic
polynomial checking uses six supported determinant permutations. These are
Python rational diagnostics, not Lean proofs and not a universal realization
theorem.

Only a pre-freeze import correction was made to the root's mathematical
draft: `Mathlib.Data.Matrix.Notation` became the installed
`Mathlib.LinearAlgebra.Matrix.Notation`. The original bytes and exact change
record are retained in `reviews/pre-freeze-draft/`. The definition bodies,
seven signatures and numerical targets were not changed.

The statement author checked pinned library APIs but has not implemented a
bridge. Newton identities exist for `MvPolynomial`; applying them to the
appropriate spectral data and justifying traces, or proving an equivalent
pure algebraic matrix recurrence, is a mandatory later proof task. A numerical
certificate for the negative rational is explicitly too narrow to discharge
that obligation.

The inspection module imports LeanCert's verification command and tests only
three definition dependencies in kernel mode. Challenge remains admitted and
cannot enter an eventual Solution import graph. A future scalar certificate
must be consumed by the negative-moment theorem and the final contradiction.
Only the standard three foundational axioms, or subsets, may support the
eventual complete exports.
