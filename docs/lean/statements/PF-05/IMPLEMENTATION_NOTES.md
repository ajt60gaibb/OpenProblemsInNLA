# PF-05 implementation correspondence

Implementation author: OpenAI Codex AI agent `/root/infra_audit`, 2026-09-28.
The exact specification was authored by `/root`. Independent preimplementation
approvals from `/root/statement_design` and `/root/inventory` were available
before this implementation was written. The implementer's earlier specification
review is retained as history and must not count as an independent approval in
the final metadata.

`PF05.Target` is a closed proposition definition. It asserts no proof of the
equivalence. Every helper expands into explicit finite real matrices and their
ordinary algebraic operations; no semantic predicates are supplied by a caller.

`PositiveSemidefinite` means literal real symmetry and a nonnegative full
quadratic-form sum for every real vector. `Factorization` requires these
conditions on every row and column factor and the exact trace of their ordinary
matrix product. `Matrix.trace` is the sum of diagonal entries in the pinned
`Mathlib/LinearAlgebra/Matrix/Trace.lean`; matrix multiplication sums products
over the common finite dimension. Scalar multiplication in the straight
segments is the usual entrywise real scalar action.

`PSDRankTwo` requires a size-two factorization and forbids size one. This is
exactly PSD rank two because the source minimizes over positive sizes.
`Matrix.rank` is the real finrank of the range of the associated multiplication
map in the pinned `Mathlib/LinearAlgebra/Matrix/Rank.lean`. Rank three already
rules out empty dimensions. Entrywise nonnegative inputs, zero rows/columns,
zero entries and singular or repeated factors are preserved.

`FeasibleDirection A E B F` requires both direction families to be real
symmetric, imposes precisely
`trace (E i * B j) + trace (A i * F j) = 0`, and quantifies one common real
`h > 0` with PSD of every `A i + t • E i` and `B j + t • F j` for every
`0 ≤ t < h`. It does not require exact factorization at positive times or
replace this condition by a tangent-cone test.

`InfinitesimallyRigid` uses one scalar `d` for all directions, with the two
opposite signs in the source. `UniqueUpToCongruence` quantifies every alternative
size-two PSD factorization, then one real square matrix `S` satisfying
`S.det ≠ 0`, `Atilde i = S.transpose * A i * S`, and
`Btilde j = S⁻¹ * B j * (S⁻¹).transpose` for all indices. In the pinned
`Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`, the inverse is defined
by the determinant/adjugate formula and satisfies both inverse identities for
a unit determinant. Over the real field, the explicit nonzero determinant
ensures that condition, so no singular-inverse fallback is used in the target.

The final target universally quantifies the input matrix and every fixed
size-two factorization and asks for both directions of the equivalence. It
adds no normalization, strict positivity, positive definiteness, probability,
objective, or computational tolerance.

The live module is compiled with pinned Lean 4.33.1, Mathlib and LeanCert.
Author development logs and source receipts are in `/private/tmp/nla-pf05-evidence`.
The target axiom closure is checked by both the shared `#assert_statement`
command and LeanCert `#assert_trust kernel`; local successful elaboration is
neither a proof of `Target` nor authoritative Linux Comparator verification.
Final independent reviewers must bind the actual source, frozen source, imports
and pins before registration.
