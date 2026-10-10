# MF-03 finite-to-infinite tableau tail: independent final review

**Independent mathematical/source reviewer:** `/root/sp14_base_proof`, 10 October 2026. **Imported signature/kernel auditor:** `/root`. **Verdict:** APPROVE the frozen finite-to-infinite cosine-tail comparison and fixed-tail tableau inequality for aggregate import. Their claims are still about finite weighted tableau sums.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/MF03/FiniteTableauInfiniteTail.lean` | `55e0d3d4c9243e984019d930d8ae1111899b4a3e77b6a1f434449ae3150c9f8a` |
| Exact mathematical precontract `FINITE_TABLEAU_INFINITE_TAIL_PRE_REVIEW.md` | `6b4a7001b1c9dab2c49e869853f022c6d281a8a222505585c95e7eed9d1472c4` |
| Independent pre-review `FINITE_TABLEAU_INFINITE_TAIL_INDEPENDENT_PRE_REVIEW.md` | `968d0f0ace855a2d9a141f703e543660c2acf27e56ebcbb4cd0f2cfcb27a2279` |
| Separate imported audit `/private/tmp/mf03-finite-tableau-infinite-tail-independent-audit.lean` | `225bd21908ef638cf6e4f6d306d0a98d04054553f8cea8e9247300cc1cd2cd1a` |

The reviewer checked the exact finite label embedding `k↦k−m`, its injectivity and factor-index preservation, the summability of the shifted cosine factors, and nonnegativity of every rectangular tableau weight. The public comparison is `finiteCosineTail N m ≤ cosineTail m` for **all** `N,m`, including `N≤m` and `m=0`. The second theorem combines the prior finite tableau inequality with this comparison and nonnegative multiplication to obtain `finiteAugTableauSum N m j ≤ finiteRectTableauSum N m * cosineTail m ^ j` for every `j≤m`, including `j=0`.

The direct pinned Lean 4.33.1 module build passed 8,718 jobs. The separate imported audit reconstructed both exact public signatures, reran LeanCert `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]`. The source scan found no proof escape. Determinant/tableau identities, finite-to-infinite determinant limits, and the full MF-03 Target remain open. Changed source bytes require a new review.
