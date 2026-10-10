# SP-11 independent pre-proof statement review

**Reviewer:** `/root/sp11_statement_independent` (AI agent), 9 October 2026.
**Verdict:** APPROVE the exact mathematical and numerical correspondence of the
canonical SP-11 problem, the frozen and live Lean targets, and the first
pre-proof review. This is approval to use the frozen target for proof
development, **not** a proof of the target or a formalization of Hall's theorem.

## Canonical scope

The permanent registry maps `SP-11` to
`eigenvalues-and-inverse-problems/SP-11/README.md`. Its complete byte-identical
copy is `docs/lean/statements/SP-11/ORIGINAL.md`. For every integer `n ≥ 1`
and every finite simple undirected graph `G` on `n` vertices, the original
question asks for some real `n × n` matrix `A` with all of the following:

1. `Aᵢⱼ = Aⱼᵢ` for all `i,j`;
2. for every `i ≠ j`, `Aᵢⱼ ≠ 0 ↔ G.Adj i j`, in **both** directions;
3. `dim_ℝ ker A ≥ δ(G)`, where `δ(G)` is the minimum of the ordinary
   vertex degrees.

This includes disconnected graphs, isolated vertices, and `n = 1`. It does
not constrain diagonal entries, magnitudes or signs of nonzero edge weights,
or positive semidefiniteness or the strong Arnold property. The constant in
the weak nullity bound is exactly `1`; there is no tolerance or probabilistic
qualification. The original also gives the equivalent minimum-rank inequality
`mr(G) ≤ n − δ(G)`. No minimum-rank operator is needed in the Lean witness
target, because it asks directly for a matrix achieving that bound.

The live `NLA.Statements.SP11.Target` and frozen
`NLA.ReviewedStatements.SP11.Target` quantify `∀ n, 0 < n → ∀ G, ∃ A`.
Their `HasPattern` definitions require full symmetry and the exact
off-diagonal equivalence. Their `MinimumDegree` definitions invoke
`G.minDegree` with classical finite-adjacency decidability. In the pinned
Mathlib source, `SimpleGraph` is symmetric and irreflexive, `minDegree` is
the minimum of finite neighbor-cardinality degrees, and its empty-type
fallback is irrelevant because `Fin n` is nonempty for `0 < n`. The final
conjunct is `MinimumDegree G ≤ n - A.rank`, where subtraction is in `ℕ`.
Pinned `Matrix.rank` is the real finrank of the range of `A.mulVecLin`,
and `rank_le_width` proves `A.rank ≤ n`; rank-nullity therefore identifies
the displayed natural difference with the real dimension of its kernel.
Thus the Lean comparison is precisely the canonical nullity comparison,
including its weak inequality and exact bound.

I independently compared the two Lean files after only removing the frozen
header and changing its namespace: the remaining source text is identical.
The `#assert_statement` and `#assert_trust kernel` commands inspect the
*definition boundary*. They do not establish a term of `Target`. The first
review correctly distinguishes this from a proof and retains every source
quantifier and edge-support condition.

## Resolution and remaining proof obligation

The canonical README and local application note credit H. Tracy Hall's
all-graph Delta Theorem, especially Theorem 3.20 and Corollaries 3.22 and
3.24 of the cited versioned preprint. They use a stronger positive
semidefinite, strong-Arnold-property exact-pattern witness with nullity at
least `δ(G)`. Forgetting those extra properties and applying rank-nullity
gives SP-11. The archived independent mathematical review reports a PASS on
Hall's essential informal proof, with stated limits; this review checked
the source-to-target deduction and did **not** independently formalize or
reprove that preprint.

**Formalization obstruction:** this repository currently has no proved Lean
theorem furnishing Hall's all-graph witness. Its faithful Gram construction,
graph ordering, genericity/non-cancellation argument, and real matrix
conversion, or a different fully proved equivalent construction, remain
necessary. Treating Hall's existence theorem as an axiom, `sorry`, an
unproved helper, or a field of an added hypothesis would leave SP-11
unproved. A proof for only connected graphs, graphs of positive minimum
degree, or a sampled graph family would not inhabit the frozen target without
separate proofs for the omitted cases. The target requires symbolic universal
reasoning; no finite numerical computation certifies it.

## Reproduction and hash-bound inputs

At repository HEAD `57023ac8fe02d1322436ce84074edfbca976e5dd`, I ran the
pinned Lean 4.33.1 binary's `lake build NLA.Statements.SP11 Reviewed.SP11`;
it completed successfully (1858 jobs). Both printed target-definition
closures contained only `propext`, `Classical.choice`, and `Quot.sound`.
This verifies elaboration and definition trust, **not truth** of `Target`.
I checked README/ORIGINAL byte equality and normalized live/frozen Lean
source equality. The following SHA-256 hashes identify the reviewed files:

| Repository-relative path | SHA-256 |
| --- | --- |
| `eigenvalues-and-inverse-problems/SP-11/README.md` | `8e3edc4c7c6c8b388ab7bbf87bc197b76756210b19338d27398af356016aa865` |
| `docs/lean/statements/SP-11/ORIGINAL.md` | `8e3edc4c7c6c8b388ab7bbf87bc197b76756210b19338d27398af356016aa865` |
| `eigenvalues-and-inverse-problems/SP-11/solution.md` | `87bc90a768d9d9910a4f4b041cee46f3821b9c7dfe89eec3c2b49b92a1a15253` |
| `references/stepaniants-sp11-sp12-2026-09-11/verification/SP-11-SP-12-independent-review.md` | `5fc9eb0cfed0af7d25415190b0fb9eaf2f16d73c6b2eead3452581870bf1eaef` |
| `docs/lean/statements/SP-11/NUMERICAL_TARGETS.md` | `a0cd200e8bd4dca2a9b0c7a690e874d67b1d4df9f7179ab9db738c4a8ee88b00` |
| `lean-statements/NLA/Statements/SP11.lean` | `7de112a24cb0b78894d495b840a77a58572cce574d5d77eda15381410c65b131` |
| `lean-statements/Reviewed/SP11.lean` | `3a294de54f52a4287ed22b80d5b0721859154b642fe3c1ac62f7d4609be38222` |
| `docs/lean/proofs/SP-11/STATEMENT_REVIEW.md` | `0471de5dfb09b5718fa6d5cbd520a8cf9981c89978b85672bd774bd70710b884` |

The inspected pinned Mathlib revision is
`0df444a360eaa60ab8c11dca51a86af692955474`. The inspected
`SimpleGraph/Basic.lean`, `SimpleGraph/Finite.lean`, and
`LinearAlgebra/Matrix/Rank.lean` files have SHA-256 hashes
`e45d2248020078b2b2f853e6c6000af23cc0808e28ef54fda0471924bc4c9f8a`,
`1aa6eeffe77fd243fb2659ceb377843206bfa62fdeeae9e64741bedadd411934`,
and `67b4fa7bee02c1806f29562718bfb34c0e1f40af5ec6a91ef91cc33610657491`,
respectively. No original statement, registry entry, frozen target, or proof
source was changed in this review.
