# SP-11 independent statement and pre-proof review 2

Reviewer: `/root/solved_inventory`, independent AI agent, 17 October 2026.
Verdict: APPROVE the unchanged concrete target for proof development. This is neither a full theorem proof nor a Linux Comparator receipt.

## Exact statement and imported meanings

I read the canonical README, byte-identical ORIGINAL, complete Stepaniants application note, source-bound specification, live and frozen Lean definitions, and statement-checking implementation. The retained target ranges over every `n ≥ 1` and every finite simple undirected graph on `Fin n`. It selects a real square matrix after the graph; symmetry holds on all entries and off-diagonal nonvanishing is equivalent to adjacency in both directions. The diagonal, edge signs and edge magnitudes are unrestricted. There is no PSD, SAP, connectivity, regularity, genericity, or positive-minimum-degree hypothesis.

I inspected the actual pinned Mathlib `minDegree` definition: it is the minimum of all finite vertex degrees, with zero only as the empty-type default. `n > 0` excludes that default. I inspected the actual `Matrix.rank`: it is the real finrank of the image of `mulVecLin`, and `rank_le_width` bounds it by `n`. Thus `MinimumDegree G ≤ n - A.rank` is the exact original kernel-dimension lower bound under finite-dimensional rank-nullity, with no natural-subtraction loss. Isolated vertices, disconnected graphs and the singleton graph remain included.

The frozen mathematical definitions match the live ones after namespace/header substitution. `#assert_statement` checks a safe closed proposition definition and its permitted axiom closure; it supplies no witness. The previous statement elaboration reports do not prove `Target`.

## Source and proof-development boundary

I directly inspected Hall's [versioned primary text](https://arxiv.org/html/2601.01211v1), including the definitions, alternating construction, greedy inequalities, complete Unique Monomial Lemma 5.14, and main deduction. Hall supplies a stronger PSD/SAP witness; Stepaniants's note correctly forgets those properties. No theorem discovery is reassigned.

For Lean, finite polynomial specialization can replace probability: construct the polynomial vectors, prove nonedge Gram entries identically zero and edge Gram polynomials nonzero, multiply the finitely many latter polynomials, and specialize at a real point where their product does not vanish. The rank bound then follows from the ambient dimension. The nonzero-polynomial proof must retain one variable family per vertex across repeated tree occurrences. The main outstanding combinatorial obligation is uniqueness of a maximal monomial despite that reuse. Dimension counting or independent input variables at each tree occurrence would not prove this. Proposition 5.12 must be used only for the earlier-vertex case; the paper's unrestricted wording is false but its valid uses have the needed ordering hypothesis.

The new `AlternatingContraction.lean` layer is an internal algebra lemma. Its alternating form is initially an arbitrary actual map; the later recursive construction must supply the concrete universal polynomial form. Such a conditional orthogonality lemma is useful support and cannot be promoted to the graph existence theorem. The output slot is first; matching a last-output convention requires the explicit slot permutation/sign bridge or a consistently first-output noncancellation proof.

## Necessary remaining gates

1. Concrete alternating polynomial coefficients and a well-founded recursion using only prior nonneighbors.
2. Exact polynomial orthogonality for every nonedge.
3. Greedy-order construction and cardinality bounds, including singleton and zero-degree cases.
4. Noncancellation in shared commuting variables for every edge; then simultaneous real specialization.
5. Gram rank bound and transport into the literal frozen `Target`.
6. Two independent final source reviews, pinned Lean/LeanCert kernel build and axiom audit, and real isolated Linux Comparator evidence before any status change.

No canonical source, preserved original, registry, status, or reviewed target was changed. No numerical interval certificate is needed; the theorem is symbolic.

## Bound repository and dependency inputs

Published starting revision: `47006df8b3a6c724a557266c891893d03e69323a`.
Pinned Lean: 4.33.1. Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`. LeanCert: `621a43d7cf21f87872392a01e874f2f1dbddc926`.

| Input | SHA-256 |
| --- | --- |
| `eigenvalues-and-inverse-problems/SP-11/README.md` | `8e3edc4c7c6c8b388ab7bbf87bc197b76756210b19338d27398af356016aa865` |
| `docs/lean/statements/SP-11/ORIGINAL.md` | `8e3edc4c7c6c8b388ab7bbf87bc197b76756210b19338d27398af356016aa865` |
| `eigenvalues-and-inverse-problems/SP-11/solution.md` | `87bc90a768d9d9910a4f4b041cee46f3821b9c7dfe89eec3c2b49b92a1a15253` |
| `docs/lean/statements/SP-11/NUMERICAL_TARGETS.md` | `a0cd200e8bd4dca2a9b0c7a690e874d67b1d4df9f7179ab9db738c4a8ee88b00` |
| `lean-statements/NLA/Statements/SP11.lean` | `7de112a24cb0b78894d495b840a77a58572cce574d5d77eda15381410c65b131` |
| `lean-statements/Reviewed/SP11.lean` | `3a294de54f52a4287ed22b80d5b0721859154b642fe3c1ac62f7d4609be38222` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Finite.lean` | `1aa6eeffe77fd243fb2659ceb377843206bfa62fdeeae9e64741bedadd411934` |
| `lean-statements/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Rank.lean` | `67b4fa7bee02c1806f29562718bfb34c0e1f40af5ec6a91ef91cc33610657491` |
