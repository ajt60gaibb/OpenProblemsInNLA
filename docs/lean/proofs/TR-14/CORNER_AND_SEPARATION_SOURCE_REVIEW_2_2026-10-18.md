# Independent corner-algebra and scalar-block review

Date: 2026-10-18. Reviewer: `/root/fr05_statement`.

Decision: **APPROVE** the five exact modules below. The fresh immutable import-closure replay passed. This is an independent review of root-authored corner algebra and solver-authored scalar-block separation. My own `ReducedSubalgebras` and `ReducedPrimitiveBlocks`, although imported and replayed, are excluded from independent implementation coverage and require the other agents' reviews.

| Module | SHA-256 |
| --- | --- |
| IdempotentCorner | e96d2e7e6d6d43b1793d717a13f329f3979628ac3ecb42fa720372f615fe5b78 |
| CornerProduct | 6a1b5920f946ba73eb8ccd3fabc3ddb9b1c2d811585b9ad643033a4cd4e955bd |
| CornerContext | f1de8589c8e0f13baaaaac6fd2df3233c257bcbb00181879b081aec327632ad1 |
| CornerStabilizer | 8c0fbebebf4a0731a3bea9b0c19128cb6c401f3ffead3f63a27bb5d1caef5ccd |
| ScalarGraphSeparation | c62f16519ed79347a40b9fd6131c4b0a711557ed9527241fe2aa4826cdbd7112 |

The idempotent block is the genuine unital quotient `B/(1-e)`. Its ambient inclusion is a linear injective map sending `[x]` to `e*x`, sends its own identity to `e`, and preserves products. The source correctly uses this multiplicative linear inclusion without asserting that it is a unital algebra map into `B`. The constructed equivalence identifies its dimension with the actual ambient multiplication-image dimension, including the zero block.

The product-corner map is an actual algebra equivalence between the corner of `A × C` and the product of the two factor corners. Reducedness is asserted only when the ambient algebra is reduced: nilpotence transports through the injective, multiplicative inclusion using positive powers. This does not impose reducedness on the potentially nonreduced moment algebra `A`.

The contextual block spaces are actual images under quotient algebra homomorphisms. Whole list products commute with those images. The block functional is the original functional composed with the actual inclusion. Stabilizer membership supplies the annihilation implication. The Frobenius restriction proves nondegeneracy by testing against the actual projected elements of the original first factor and applying injectivity; no block nondegeneracy or dimension hypothesis is assumed. One-containing mode spaces and first-projection surjectivity are also transported by actual quotient maps.

For a primitive indicator of the actual full stabilizer, a stabilizer of the intrinsic block extends through the actual inclusion to an ambient stabilizer. The independently specified primitive scalar-action identity forces it to equal a scalar multiple of the block identity. The finrank bound is therefore derived from actual containment in the span of that identity. It is not a supplied one-dimensional-stabilizer premise.

The scalar-block separation proof uses the displayed hypotheses exactly: the actual whole product surjects onto scalar coordinates, the functional annihilates the product, and each scalar-coordinate functional coefficient is nonzero. A stabilizing multiplier with zero quotient component acts on a chosen scalar-coordinate preimage as a scalar multiple of that coordinate indicator. Functional evaluation forces every scalar component to vanish. Thus a nonzero actual primitive indicator has nonzero quotient component. These hypotheses remain visible in the generic theorem and must be supplied by the ordinary graph construction in the final application.

No target, original problem page, numerical convention, or permanent ID is changed. These five modules are supporting gates for the all-width complex bilinear TR-14 target, and alone do not prove the final ordinary lower bound or full Target. They make no Linux/Comparator or catalog-status claim.

Reproducible evidence: `26` exact source modules were copied into a private immutable snapshot and freshly compiled, in dependency order, into private objects with pinned Mathlib/LeanCert dependency caches only. All `26` commands passed. Every source hash matched the live source before and after the build. All printed axiom closures were subsets of `[propext, Classical.choice, Quot.sound]`, and all source `#assert_trust kernel` checks passed. The attached `corner-source-review-2-evidence-2026-10-18/result.json`, per-module logs, full snapshot, and `check-build.py.txt` retain the source hashes and exact commands. This replay did not use NLA objects from another agent and did not mutate shared caches.
