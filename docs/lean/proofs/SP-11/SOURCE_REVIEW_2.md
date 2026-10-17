# SP-11 independent partial-source review 2

Reviewer: `/root/solved_inventory`, AI agent, 17 October 2026.
Verdict: **APPROVE the four coordinator-authored support modules below at the recorded hashes, within their explicit conditional scope.** This is not approval of a full SP-11 proof or a status promotion.

## Independence and exact scope

I did not author or modify `GramBridge.lean`, `PolynomialFaithfulness.lean`, `UniformLSS.lean`, or `PolynomialLSS.lean`. I read each full source, independently compiled each with the pinned Lean 4.33.1 development runner, and retained the command logs and immutable source hashes in [review-2-evidence/result.json](review-2-evidence/result.json). Every run succeeded and source bytes remained unchanged during it. LeanCert kernel assertions passed; the exported audit lines list only `propext`, `Classical.choice`, and `Quot.sound`.

I authored the imported `AlternatingContraction.lean` and `AlternatingPolynomial.lean` support modules. Their hashes are included to bind the reviewed closure, but **this report is not an independent review of those two modules**. They require the separate reviewer's audit. The exact target correspondence is separately reviewed in [STATEMENT_REVIEW_2.md](STATEMENT_REVIEW_2.md).

## Mathematical and semantic checks

`GramBridge` forms the actual real Gram matrix `R * R.transpose`. Symmetry is entrywise commutativity, the complete off-diagonal equivalence is transferred without strengthening the target, and rank is bounded by the actual ambient width. The dimension hypothesis is exactly `d + MinimumDegree G ≤ n`; natural arithmetic gives the source nullity lower bound without assuming that the vector rows span the ambient space. Its final theorem explicitly requires a faithful representation for every positive dimension and graph. It does not assert that such a representation has been constructed.

`PolynomialFaithfulness` uses concrete `MvPolynomial` operations. Nonzero real polynomials have an actual nonvanishing real evaluation by polynomial extensionality over the infinite field. The finite product argument handles every required constraint simultaneously, including an empty constraint family. Evaluation preserves all Gram products and sums. The two polynomial premises are complete: every distinct nonedge vanishes identically, and every edge and diagonal is a nonzero polynomial. These yield both directions of the exact pattern and nonzero rows; the universal target theorem retains these premises as unproved witness obligations.

`UniformLSS` lists exactly the strictly earlier nonneighbors, sorts them in the fixed increasing order, and accesses actual list entries. The strict index decrease proves well-foundedness. `WellFounded.fix_eq` gives the literal contraction recurrence. Alternation implies exact orthogonality to every predecessor, then commutativity of the bilinear dot product and graph symmetry cover every distinct nonedge in either order. The zero form and zero vectors are allowed at this stage, correctly: there is no unsupported nonvanishing or dimension claim.

`PolynomialLSS` instantiates that actual recursion in one polynomial ring. Its dependent Sigma variable index contains a vertex and an increasing coordinate subset of precisely that vertex's arity. Repeated recursive occurrences use the same vertex form and variables. It therefore preserves the cancellation problem rather than bypassing it with independent occurrence variables. The polynomial nonedge identity is unconditional. Its matrix-existence theorem is explicitly conditional on the complete diagonal/edge nonvanishing obligation and the ambient-dimension bound. No free semantic field, assumed graph invariant, axiom, `sorry`, or native computation enters these four proof closures.

## Remaining gap and verification limits

The support program does not establish the nonzero diagonal/edge Gram polynomials for greedy graph orderings, or the final unconditional all-graph theorem. Hall's shared-variable Unique Monomial Lemma or a genuinely proved equivalent remains necessary. The conditional reduction must not be advertised as the retained problem's solution.

The retained runs are local development elaborations with kernel trust assertions and axiom reports. They are not a fresh isolated Linux sandbox or Comparator acceptance receipt. Final proof/statement comparison, two independent full-source reviews and the authoritative Linux checks remain required for promotion. No canonical page, ORIGINAL, registry or status was modified by this review.

## Hash-bound inputs

| Source | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP11/GramBridge.lean` | `e3ff1bd936a820a58ac005dd50487464e8d5a56b231268bd1e1b5d9936ab1aed` |
| `lean-statements/NLA/Proofs/SP11/PolynomialFaithfulness.lean` | `e1214cdc4072420c86006538cc9465bf29e9dda5a5e72dd1a0eb9ace4fd7928c` |
| `lean-statements/NLA/Proofs/SP11/UniformLSS.lean` | `485ffa227d00a09bc93b8fe244815e8e7dc912064edffa6cadc8f09fc52bd431` |
| `lean-statements/NLA/Proofs/SP11/PolynomialLSS.lean` | `12f18f17f1d74e03cd14a9b42bf9dfc45f67a0239f5cc8e0e405f45a267efd66` |
| `lean-statements/NLA/Proofs/SP11/AlternatingContraction.lean` | `5470ac391cec624ed4a11bc3fe5ff271dccbc2446db8a4aac44053c01407b6ca` |
| `lean-statements/NLA/Proofs/SP11/AlternatingPolynomial.lean` | `d1ece1a3defce0f4cae49af934548c2bad20d7273a7df91b29111787d8c876f7` |
| `lean-statements/NLA/Statements/SP11.lean` | `7de112a24cb0b78894d495b840a77a58572cce574d5d77eda15381410c65b131` |
| `lean-statements/Reviewed/SP11.lean` | `3a294de54f52a4287ed22b80d5b0721859154b642fe3c1ac62f7d4609be38222` |
