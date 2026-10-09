# SP-12 specification review

Reviewer: OpenAI Codex agent `/root/inventory` (AI), independent of specification author `/root`.

Phase: `specification`. Verdict: **APPROVED**.

The complete canonical README and retained ORIGINAL.md were read and checked byte for byte against each other. This review occurred before implementation of the target.

- `eigenvalues-and-inverse-problems/SP-12/README.md`: `cdc8003bc5160604408ce6b95c344a4ea1b9bfbf8af0f99ae1e8e016648d53e1`
- `docs/lean/statements/SP-12/NUMERICAL_TARGETS.md`: `6dae7d486ecaeab1903b31e816e34f57fef417ef15627574f4c4a307b902cae7`
- `docs/lean/statements/SP-12/ORIGINAL.md`: `cdc8003bc5160604408ce6b95c344a4ea1b9bfbf8af0f99ae1e8e016648d53e1`

The specification keeps every simple graph on n >= 1 vertices and seeks a single real symmetric matrix with exactly the graph off-diagonal nonzero pattern. Diagonal entries remain unrestricted beyond PSD and SAP.

The PSD condition is the real quadratic-form nonnegativity condition. SAP correctly quantifies over all real symmetric X and preserves three separate exact requirements: ordinary A*X=0, the entrywise products A(i,j)X(i,j)=0, and zero diagonal of X. The final requirement is exactly I Hadamard X=0, not the stronger ordinary product I*X=0.

The coloring invariant is a concrete least natural number admitting a proper vertex coloring, with finite colors Fin c. The n-color labeling witnesses nonemptiness; n>=1 prevents a coloring with zero colors. Thus natural chi-1 has the intended value, including chi=1.

The witness form is equivalent to the displayed maximum-nu inequality. Feasible nullities are integers bounded by n and the feasible set is nonempty: a sufficiently large positive diagonal plus the adjacency matrix is positive definite with the required pattern, and its invertibility implies SAP. Hence the maximal feasible nullity is attained.

Nullity as natural n-rank(A) is exact by finite-dimensional real rank-nullity and rank(A)<=n. The definition admits rank-zero matrices when their pattern and SAP permit them; no vertex-critical, connectedness or probability restriction is introduced.

The specification is sufficient for implementation. Actual PSD/rank/least-natural APIs and all elaborated index fields remain independent Lean-boundary obligations.

Independent specification correspondence review only. No Lean implementation, mathematical proof, cited-paper verification, or kernel/Comparator execution is certified.
