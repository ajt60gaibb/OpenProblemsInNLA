# Inspected pinned APIs and remaining work

This is a feasibility note, not a proof. Mathlib is pinned to
`0df444a360eaa60ab8c11dca51a86af692955474`. `Inspect.lean` freshly typechecked
the principal interfaces listed below using the clean read-only dependency cache; the
raw log records their actual signatures. No theorem implementing IS-03 is
declared here.

| Actual pinned API | Appropriate use and limit |
| --- | --- |
| `Matrix.charpoly_fromBlocks_zero₁₂`, `Matrix.charpoly_fromBlocks_zero₂₁`, `Matrix.charpoly_reindex` | Use the witness's `1+2+4` block structure and a proved index equivalence. Small exact block determinants can avoid expanding a generic order-seven determinant. |
| `Matrix.charpoly_monic`, `Matrix.charpoly_natDegree_eq_dim` | Actual characteristic polynomials are monic of the matrix order; polynomial equality can transport this to the displayed derivative once established. |
| `Matrix.trace_eq_neg_charpoly_coeff` | Gives the first trace from a characteristic coefficient. It is not a theorem for all power traces. |
| `Matrix.trace_eq_sum_roots_charpoly_of_splits`, `Matrix.trace_eq_sum_roots_charpoly` | Gives the trace as a multiset sum of characteristic roots. Applying it to `B^k` does not by itself identify those roots with powers of the roots of `B`. The module documentation explicitly warns against using the set of eigenvalues in place of algebraic multiplicities. |
| `MvPolynomial.psum_eq_mul_esymm_sub_sum` | Actual Newton power-sum recurrence for finitely many variables, proved in `RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean`. |
| `MvPolynomial.aeval_esymm_eq_multiset_esymm`, `MvPolynomial.psum` | Evaluate the symmetric identities at a finite family and retain multiplicity through the mapped finite-index multiset. A full coefficient/spectral correspondence still must be supplied. |
| `Matrix.aeval_self_charpoly`, `Matrix.pow_eq_aeval_mod_charpoly` | Actual Cayley–Hamilton and reduction of matrix powers. These can reduce higher powers once the initial traces are established; Cayley–Hamilton alone does not supply all six initial trace values. |
| `Matrix.derivative_det_one_add_X_smul` | Gives the first derivative of `det(1 + X M)` evaluated at zero. It is not already a full polynomial Jacobi/adjugate derivative identity. |

`Matrix.charpoly` and `Matrix.charmatrix` were inspected in full at their
definition sites; the Cayley–Hamilton proof transports the genuine adjugate
identity through `Matrix.matPolyEquiv`. This suggests an alternative exact
coefficient recurrence, but that recurrence is not present as an IS-03 lemma.

`LinearAlgebra/Eigenspace/Triangularizable.lean` supplies generalized-eigenspace
decomposition and existence of eigenvalues over an algebraically closed
field. Its TODO still calls for a general definition of triangularizability
and an equivalence with generalized-eigenspace spanning. Merely importing
this module must not be described as having an already available ordered
matrix Schur-form theorem.

The significant remaining foundation is therefore the **actual arbitrary
real matrix** characteristic-polynomial-to-power-trace bridge. The author
has not found a direct named theorem that discharges it in one application.
Possible proof routes include the symmetric/root route with a proved
multiplicity-preserving matrix bridge, or a proved adjugate/determinant
coefficient recurrence. Neither may be assumed as an axiom. The frozen
statement remains independent of this implementation choice.

The source witness and finite rational arithmetic are small. The planned
LeanCert singleton `-8593/823543 < 0` should use no subdivision or approximate
root analysis, and it certifies only the scalar sign. Exact algebraic
identities and a complete trace bridge carry the substantive matrix argument.
