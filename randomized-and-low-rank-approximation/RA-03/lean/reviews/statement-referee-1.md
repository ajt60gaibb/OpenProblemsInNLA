# RA-03 independent statement referee 1

Date: 2026-09-12. Reviewer: OpenAI Codex AI agent `/root`.
The reviewer did not author these definitions or Challenge declarations.
This is AI-agent review, not human peer review.

**Verdict: approve the frozen statement boundary for proof implementation.**
The separate second statement approval is also required. No Lean solution
or final verification result is established by this statement review.

I read the canonical RA-03 README and the complete Colbrook random-pivoting
manuscript at upstream `e7252e5307781a7c897bca6cb124f6ab838f6809`, including
its separate Cholesky, asymptotic-sharpness and correlation-matrix results.
Only the Section 2 randomized-LU counterexample is needed for this project's
full negative answer. I read the complete proposed definitions, Challenge and
numerical obligations, and the actual pinned Mathlib singular-value and
matrix-norm definitions.

- The canonical target is randomized **LU**, with jointly sampled row/column
  entries weighted by squared complex modulus. The definition retains every
  complex rectangular matrix, both positive dimensions and every allowed
  `1≤k≤min(m,n)`. No symmetry, positivity, nonsingularity or real-only premise
  is added to the universal conjecture.
- The residual update uses the actual selected column and row with the
  original pivot denominator. The function's identity update at a zero entry
  can only occur on a zero-mass entry transition. A nonzero residual has zero
  mass at `none`; a zero residual has mass one there and remains zero. These
  totalizations therefore implement the canonical absorption convention and
  do not change any positive-probability algorithm path.
- `historyResidual` applies all transitions in order. `historyMass` multiplies
  the conditional masses recomputed at each actual residual. It neither
  assumes independent row and column sampling nor treats successive pivot
  choices as identically distributed. `expectedError` sums all finite
  histories, weighted by their joint masses.
- The required generic `process_isProbability` export proves nonnegativity
  and normalization of both one-step and arbitrary-length history masses.
  Thus the finite weighted sum is an ordinary expectation, not an unnormalized
  surrogate. Generic absorption and probability assertions must be proved;
  the declaration does not assume them.
- `frobeniusSq` is the exact sum of complex squared moduli. The separate
  `frobeniusSq_eq_norm_sq` declaration explicitly opens Mathlib's Frobenius
  matrix norm scope. It does not equate the entry sum with the default
  entrywise supremum norm. All matrix dimensions, including empty dimensions
  for the supporting probability/norm statements, have finite index types.
- `singularValue` calls the actual singular values of `Matrix.toEuclideanLin`.
  Mathlib defines these as nonnegative square roots of the ordered
  adjoint-composition eigenvalues, with multiplicity and zero extension.
  Its proved antitone ordering and rank support give the standard singular
  values. The zero-based tail `[k,min(m,n))` is exactly the original one-based
  tail `j>k`; no best-approximation matrix or alleged spectrum is assumed.
- The witness tables occur only on the conclusion sides of required
  equalities. Actual pivot probabilities, actual residual errors, the real
  finite expectation, the actual ordered singular values and their tail all
  remain obligations. The concrete strict reverse inequality refutes the
  full quantified conjecture, not merely a separately defined one-step claim.

I independently reconstructed all four exact rational rank-one updates.
The diagonal probabilities are `2/5` with error `9/4`; the off-diagonal
probabilities are `1/10` with error `9`. Every contribution is `9/10`, so
the expectation is `18/5`. The actual Gram matrix is `[[5,4],[4,5]]`, with
independent eigenvectors `(1,1)` and `(1,-1)` for eigenvalues 9 and 1;
the ordered singular values are 3 and 1. The rank-one squared tail is one
and the proposed bound is two. The [exact reconstruction record](statement-referee-1-numerics.json)
is supplementary evidence, not a Lean proof.

I independently ran `lake build NLA.RA03.Definitions Challenge`: exit zero,
2723 build graph jobs using the existing dependency cache. The only warnings
were the four intentional Challenge placeholders. No implementation or
statement change was made by this referee.

The design supports exact finite algebra, generic inductive probability
normalization and spectral identities. It does not require arbitrary-dimensional
history enumeration, numerical eigensolves or interval subdivision. LeanCert
can be confined to the final rational scalar gap after all bridges are proved.
This fits the requested computational minimization without narrowing the target.

| Frozen file | SHA256 |
|---|---|
| `NLA/RA03/Definitions.lean` | `de6509ef6b4a41db3e01fce7b77af4c7c338dbd61f8f135e956602d3b8b0980f` |
| `Challenge.lean` | `74a7c727e8cf2fa1ee26e78cfab812626b265abe8211e09f144a3c78fca5345e` |
| `NUMERICAL_TARGETS.md` | `91618c7848ad46931a8f59bad6ff2900bf53b1e1dde22f31383c4a3941eb4a94` |

Colbrook retains informal mathematical authorship. George Stepaniants receives
formalization credit with his approved department and university affiliation;
no contact email is added. The relevant Tau Ceti fidelity, scope, documentation
and attribution principles are satisfied at the statement stage. Any substantive
statement change reopens this review. Final independent proof reviews, axiom
checks, Comparator and immutable publication evidence are still required.
