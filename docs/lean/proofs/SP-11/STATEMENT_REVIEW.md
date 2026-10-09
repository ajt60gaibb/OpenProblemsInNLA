# SP-11 pre-proof statement review

**Reviewer:** `/root/next_solved_triage` (AI agent), 9 October 2026.
**Status:** Exact canonical mathematics, numeric scope, and frozen Lean
statement reviewed. This is a pre-proof review, not a Lean proof or an
independent second approval. No SP-11 proof module was implemented here.

## Selection and feasibility

SP-11 has a particularly direct statement boundary among the remaining
Solved targets: one finite simple graph, one real symmetric matrix witness,
an exact off-diagonal zero pattern, and one natural-number rank bound. There
are no random laws, limits, exact-real algorithms, complexity classes, or
numerical certificates in the target. The frozen target already uses Mathlib's
finite graph and real matrix types. This makes it a useful next **proof
development candidate** beside MF-03, but its short final deduction must not
be mistaken for a short complete formal proof.

The major unresolved formalization input is Hall's all-graph Delta Theorem.
The canonical resolution uses a positive-semidefinite strong-Arnold-property
matrix of nullity at least the graph's minimum degree. Hall's Theorem 3.20
and Corollary 3.22 obtain this through the uniform Lovász–Saks–Schrijver
construction and a substantial non-cancellation argument. Neither that
theorem nor an equivalent all-graph matrix construction is currently a
proved theorem in this repository's Lean development. It must be proved in
Lean, or replaced by a genuinely proved equivalent route; introducing it as
an axiom, class field, or unproved helper would not prove SP-11. The archived
application note proves only the final implication from Hall's theorem.

## Exact canonical mathematical target

The permanent registry maps `SP-11` to
`eigenvalues-and-inverse-problems/SP-11/README.md`. For **every** integer
`n ≥ 1` and **every** finite simple undirected graph `G` on `n` vertices,
there must **exist** one real `n × n` matrix `A` such that:

1. `Aᵢⱼ = Aⱼᵢ` for every pair of vertices;
2. for every **distinct** `i,j`, `Aᵢⱼ ≠ 0` **if and only if** `i` and `j`
   are adjacent in `G`;
3. `dim_ℝ ker A ≥ δ(G)`, equivalently
   `rank_ℝ A ≤ n − δ(G)`.

The diagonal entries are unrestricted. The edge weights can be any nonzero
reals, may vary by edge, and are not prescribed or required to be positive.
The target does not require positive semidefiniteness, the strong Arnold
property, connectedness, regularity, a girth bound, or an optimal-rank
classification. The graph may have isolated vertices; `n = 1` is included.
All inequalities are weak, and the constant in the rank/nullity bound is
**exactly one**. The witness may depend on `G` and `n`; there is no uniform
matrix formula or algorithmic time bound in the original problem.

The frozen `NLA.Statements.SP11.Target` expresses precisely this witness
form. Its quantifier order is `∀ n, 0 < n → ∀ G, ∃ A`. `HasPattern G A`
conjoins all-index symmetry with the complete off-diagonal equivalence.
`MinimumDegree G` unfolds to Mathlib `G.minDegree`, the minimum of the
ordinary finite neighbor cardinalities; the guard `0 < n` makes `Fin n`
nonempty, so the empty-vertex default of Mathlib's definition never changes
the target. The final conjunct is

```lean
MinimumDegree G ≤ n - A.rank
```

with natural subtraction. For an `n × n` real matrix, `A.rank ≤ n`; real
rank-nullity then identifies `n - A.rank` with `dim_ℝ ker A`. This is the
canonical nullity assertion, not a weaker numerical surrogate. The live and
frozen `Reviewed.SP11` source definitions agree apart from namespace and
header text. Their `#assert_statement` and `#assert_trust kernel` commands
check the *definition boundary*, not a proof of the proposition.

## Source resolution and proof boundary

The canonical resolution credits H. Tracy Hall's
[versioned preprint](https://arxiv.org/html/2601.01211v1), Theorem 3.20 and
Corollaries 3.22 and 3.24. The independently reviewed local application note
states Hall's stronger conclusion as `ν(G) ≥ δ(G)`, where `ν` maximizes
nullity over real positive-semidefinite exact-pattern matrices satisfying
the strong Arnold property. Forgetting PSD and SAP leaves a matrix admitted
by SP-11. Rank-nullity gives the exact chain

```text
δ(G) ≤ dim ker A = n − rank A.
```

The positive-semidefinite/SAP witness is a **stronger proved source input**,
not an additional assumption on the SP-11 domain. The local solution's
last deduction is elementary. The entire Hall existence theorem, including
the graph ordering, faithful Gram construction, genericity/non-cancellation,
and real matrix conversion, is the substantive formal proof obligation.
The preliminary Mathlib searches found graph minimum-degree lemmas and matrix
rank infrastructure, but no pre-existing theorem that supplies Hall's
all-graph matrix witness. No finite sample or numerical graph-atlas check can
establish the universal claim.

A kernel-checked SP-11 proof should export a theorem with the literal frozen
`NLA.Statements.SP11.Target` type, then pass the shared Comparator and
LeanCert kernel audit. The pinned `lake build NLA.Statements.SP11
Reviewed.SP11` passed (1858 jobs); each target definition reported only
`propext`, `Classical.choice`, and `Quot.sound` in its axiom closure. This
confirms elaboration and definition trust, not truth. If one formalizes the
stronger Hall theorem first,
the final transport must preserve every graph, every dimension `n ≥ 1`, and
the full `Aᵢⱼ ≠ 0 ↔ G.Adj i j` pattern. A theorem only for connected or
positive-minimum-degree graphs needs separate proofs for excluded cases;
it cannot silently replace this target. There is no meaningful bulk numeric
computation to optimize in the SP-11 target; proof work should use symbolic
finite graph and linear algebra lemmas.

## SHA-256 of reviewed repository inputs

Repository revision at review: `57023ac8fe02d1322436ce84074edfbca976e5dd`.
The source and frozen statement files below were not edited.

| Repository-relative path | SHA-256 |
| --- | --- |
| `eigenvalues-and-inverse-problems/SP-11/README.md` | `8e3edc4c7c6c8b388ab7bbf87bc197b76756210b19338d27398af356016aa865` |
| `eigenvalues-and-inverse-problems/SP-11/solution.md` | `87bc90a768d9d9910a4f4b041cee46f3821b9c7dfe89eec3c2b49b92a1a15253` |
| `eigenvalues-and-inverse-problems/SP-11/solution.tex` | `a639991609d402f107035c9e970519273237dd4fee838bd91ee23a0ba71ac0d8` |
| `references/stepaniants-sp11-sp12-2026-09-11/verification/SP-11-SP-12-independent-review.md` | `5fc9eb0cfed0af7d25415190b0fb9eaf2f16d73c6b2eead3452581870bf1eaef` |
| `docs/lean/statements/SP-11/NUMERICAL_TARGETS.md` | `a0cd200e8bd4dca2a9b0c7a690e874d67b1d4df9f7179ab9db738c4a8ee88b00` |
| `lean-statements/NLA/Statements/SP11.lean` | `7de112a24cb0b78894d495b840a77a58572cce574d5d77eda15381410c65b131` |
| `lean-statements/Reviewed/SP11.lean` | `3a294de54f52a4287ed22b80d5b0721859154b642fe3c1ac62f7d4609be38222` |

Pinned local toolchain: Lean `v4.33.1`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. The Mathlib `minDegree`
definition reviewed is in `Mathlib/Combinatorics/SimpleGraph/Finite.lean`
(SHA-256 `1aa6eeffe77fd243fb2659ceb377843206bfa62fdeeae9e64741bedadd411934`).
