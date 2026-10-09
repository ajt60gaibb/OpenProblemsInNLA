# SP-11 specification review

Reviewer: OpenAI Codex agent `/root/inventory` (AI), independent of specification author `/root`.

Phase: `specification`. Verdict: **APPROVED**.

The complete canonical README and retained ORIGINAL.md were read and checked byte for byte against each other. This review occurred before implementation of the target.

- `eigenvalues-and-inverse-problems/SP-11/README.md`: `8e3edc4c7c6c8b388ab7bbf87bc197b76756210b19338d27398af356016aa865`
- `docs/lean/statements/SP-11/NUMERICAL_TARGETS.md`: `a0cd200e8bd4dca2a9b0c7a690e874d67b1d4df9f7179ab9db738c4a8ee88b00`
- `docs/lean/statements/SP-11/ORIGINAL.md`: `8e3edc4c7c6c8b388ab7bbf87bc197b76756210b19338d27398af356016aa865`

The graph domain is every finite simple undirected graph on n >= 1 vertices. Labeling vertices by Fin n is an exact finite indexing convention, not a restriction on graph isomorphism classes. Disconnected, isolated-vertex and singleton cases are retained.

The matrix must be real and symmetric, with A(i,j) != 0 if and only if adjacency for distinct indices. The bidirectional condition imposes exactly the source sparsity pattern; there is no diagonal, edge-weight sign, PSD or SAP restriction.

The witness nullity lower bound is the original displayed statement. In finite real dimension rank(A) <= n, and rank-nullity identifies natural n-rank(A) with kernel dimension without truncation error. The intended minDegree is the minimum of all ordinary vertex degrees on this nonempty vertex set.

The existential matrix is selected after the complete graph. No connectivity, girth, regularity, genericity, algorithm or stronger source-resolution conclusion is added. Equivalence to the source minimum-rank formulation follows from the same finite rank-nullity identity.

The specification is sufficient for implementation. The actual Mathlib rank and minDegree definitions and their real-field/nonempty-type specialization must still be checked during the Lean-boundary review; this approval does not pre-certify an API call.

Independent specification correspondence review only. No Lean implementation, mathematical proof, cited-paper verification, or kernel/Comparator execution is certified.
