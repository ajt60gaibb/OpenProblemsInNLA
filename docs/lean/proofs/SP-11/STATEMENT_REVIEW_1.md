# SP-11 fresh independent statement and proof-route review

Reviewer: `/root/fr05_statement` (independent AI agent), 17 October 2026.
Baseline: `47006df8b3a6c724a557266c891893d03e69323a`.
Verdict: **APPROVE the unchanged exact statement for proof development.**
This review does not certify a proof of `Target` or Hall's entire theorem.

## Actual statement bytes

I read the canonical README, ORIGINAL snapshot, numerical specification,
application note, actual live and frozen Lean files, and the prior reviews.
Fresh byte comparisons confirm README equals ORIGINAL and that live and
frozen Lean files agree after removing only the frozen header and changing
`NLA.ReviewedStatements.SP11` to `NLA.Statements.SP11`.

The exact target requires, for every positive natural `n` and every simple
undirected graph on `Fin n`, one real symmetric square matrix. Its nonzero
entries at distinct indices must correspond to adjacency in both directions.
The diagonal is unrestricted. There are no connectivity, degree, regularity,
PSD, SAP, sign, or genericity assumptions. Singleton graphs, disconnected
graphs and isolated vertices remain included. The witness is selected after
the entire graph, and the weak lower bound on nullity is exactly the minimum
degree, with coefficient one.

The frozen actual definition expresses this as
`MinimumDegree G ≤ n - A.rank`. Pinned Mathlib `Matrix.rank` is real finrank
of the range of the matrix's linear map. `rank_le_width` bounds it by `n`, so
rank-nullity gives the exact kernel dimension and natural subtraction loses
nothing. `SimpleGraph.minDegree` minimizes the ordinary finite neighbor
cardinalities. The positive-size guard makes the vertex type nonempty, so
its empty-type fallback is irrelevant. `HasPattern` explicitly retains both
directions of the support equivalence and all-index symmetry. The statement
assertion and kernel-trust checks on the *definition* do not prove its truth.

| Reviewed input | SHA-256 |
| --- | --- |
| `eigenvalues-and-inverse-problems/SP-11/README.md` and `docs/lean/statements/SP-11/ORIGINAL.md` | `8e3edc4c7c6c8b388ab7bbf87bc197b76756210b19338d27398af356016aa865` |
| `eigenvalues-and-inverse-problems/SP-11/solution.md` | `87bc90a768d9d9910a4f4b041cee46f3821b9c7dfe89eec3c2b49b92a1a15253` |
| `docs/lean/statements/SP-11/NUMERICAL_TARGETS.md` | `a0cd200e8bd4dca2a9b0c7a690e874d67b1d4df9f7179ab9db738c4a8ee88b00` |
| `lean-statements/NLA/Statements/SP11.lean` | `7de112a24cb0b78894d495b840a77a58572cce574d5d77eda15381410c65b131` |
| `lean-statements/Reviewed/SP11.lean` | `3a294de54f52a4287ed22b80d5b0721859154b642fe3c1ac62f7d4609be38222` |

## Primary-source route

I read the needed construction and proof in [Hall's versioned primary text](https://arxiv.org/html/2601.01211v1),
Sections 3.2-3.7, 4 and 5, including the complete Unique Monomial Lemma 5.14
and the final proof of Theorem 3.20. The source uses greedy vertex ordering,
alternating multilinear node variables, and recursively composed polynomial
vectors. Repeated inputs force orthogonality at nonedges. Greedy precursor
count inequalities control a lexicographic non-cancellation argument at
edges. A common parameter assignment avoids the finitely many required
polynomial zero sets. Taking the Gram matrix yields a faithful matrix in
dimension `n - degree(last)`, hence rank at most `n - minDegree`. The source
also proves PSD/SAP conclusions, which the retained SP-11 target does not
require. The application note's short deduction does not replace the
substantive construction or non-cancellation proof.

## Reusable infrastructure and practical proof gates

The following are concrete implementation judgments, not assumed external
theorems. The pinned Mathlib revision is
`0df444a360eaa60ab8c11dca51a86af692955474`.

- `Finset.exists_min_image` and `Finset.strongInductionOn` suffice to build a
  complete duplicate-free greedy listing. `List.Nodup.getEquivOfForallMemList`
  turns that listing into a genuine vertex-order equivalence.
- Prefixes represented by `List.take` and `List.toFinset` give exact earlier
  nonneighbor cardinalities. Finset inclusion gives monotonicity; the greedy
  choice compares a chosen vertex with every still-unchosen vertex. Counting
  before a child gives its zero-based position and thus the strict one-based
  inequality. This is a viable substantial first proof gate.
- `SimpleGraph.degree_compl` and `minDegree_le_degree` give the exact final
  count/dimension identity and the minimum-degree dimension inequality.
- Alternating maps already have `map_eq_zero_of_eq` and
  `map_eq_zero_of_not_injective`; matrix multiplication and transpose already
  have the rank inequalities needed for the final Gram step. These APIs
  discharge local algebra; they supply no all-graph faithful representation.
- The hard next gate is a literal, finite polynomial construction with proved
  orthogonality and a proved nonzero coefficient for every required edge
  inner product. Choosing nonzero vectors in available orthogonal complements
  alone is insufficient. The proof must control accidental zero inner
  products. A finite product of the required nonzero polynomials can replace
  probability arguments if its nonzero evaluation is proved over the reals.

The full-target acceptance criterion remains an unconditional theorem of the
literal frozen `Target` type, plus independent review, Comparator acceptance
and LeanCert kernel checks of that theorem. A conditional Gram bridge or
completed ordering module is explicitly partial progress. No Hall theorem,
faithfulness invariant or non-cancellation result may be added as an axiom or
unproved hypothesis to claim completion.

This reviewer is implementing `NLA/Proofs/SP11/GreedyOrdering.lean` separately;
that contribution is not an independent review of its own proof. The other
agent's `GramBridge.lean` was read: its dot-product support hypothesis is
explicit, its symmetry argument is exact over the reals, and its rank bound
works without any independence hypothesis. Its final theorem correctly
retains faithful-representation existence as an unfulfilled premise. It does
not claim to prove SP-11 unconditionally.

No canonical problem, ID, frozen boundary, original snapshot, or catalog
status was changed by this review.
