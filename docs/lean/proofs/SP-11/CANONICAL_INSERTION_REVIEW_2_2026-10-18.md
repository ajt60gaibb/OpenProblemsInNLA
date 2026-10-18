# Independent review 2: canonical pair, insertion and recovery infrastructure

Reviewer: `/root/solved_inventory`, independent AI agent, **18 October 2026**.
Verdict: **APPROVE the eight sources at the SHA-256 hashes below within their stated support scope. No blocker found. This is not a full SP-11 proof or permission to promote its status.** I did not author or edit any of these eight modules.

## Fresh verification and limits

I read all 833 source lines and ran eight fresh local pinned Lean compilations, recording the actual command, output, source hash before compilation, source unchanged-during-run check, and exit code. Every run passed. The [results](canonical-review-2-evidence-2026-10-18/result.json) and individual logs bind the inspected bytes. Their LeanCert kernel assertions passed; printed proof closures contain only `propext`, `Classical.choice`, `Quot.sound`. This is independent local elaboration evidence, not a fresh isolated Linux Comparator receipt or a substitute for the separate comprehensive snapshot audit.

The unchanged imported SP-11 target remains every graph in every positive dimension, with real symmetry, exact bidirectional off-diagonal pattern and nullity at least minimum degree. These modules neither edit that proposition nor insert a purported proof of the all-graph result.

## Exact source checks

**CanonicalColoring.** Normal children receive their zero-based sibling colors; the supplied root output must be at least its input arity. The proof uses every actual child's arity bound, including arity zero. The inserted coloring gives the cap its actual position `p` and each child `p.succAbove s`, so precisely one position is skipped. All positions `0,...,k`, including insertion first and last, lie below the stated ambient dimension. Root injectivity and recursive admissibility use the literal finite tuples; no genericity or favorable insertion position is assumed. The actual LSS trees inherit these structural facts by well-founded induction and the proved greedy child-arity inequality.

**CanonicalPair.** The two full tree colorings share one cap color, and pairColorings restores the exact original left and right colorings. The cap position is the count of the later root's predecessors strictly below the earlier root label. The earlier root's own arity is at most this count by the correctly scoped greedy inequality with `i ≤ j`; the later root uses the inserted coloring. Equal roots are included: the cap comes after all original predecessor colors. Admissibility implies every actual local sign is nonzero and their finite product is nonzero over the stated domain. The source correctly permits canonical admissibility even for nonedge pairs while claiming no Gram nonvanishing from it; cancellation can still occur.

**CanonicalOutputs.** Every ordinary input is exactly its zero-based slot, and every proper descendant of the later top root retains that rule. At the exceptional top root the coordinate is exactly `p.succAbove s`. The Fin cast transports only the proved root-arity equality; it changes no color value. These are exact equalities on actual occurrence paths, not statements about a separately chosen model.

**PriorInsertion and AugmentedColors.** The adjacency premise excludes a duplicate inserted root from the old nonneighbor list. The actual sorted augmented list has length `k+1`; its inserted entry is at the count of old entries below it. The succAbove theorem recovers every old predecessor in its original relative order, with no endpoint dropped. Its proof uses strict monotonicity and equality of full finite ranges. AugmentedColors is literal insertNth: cap and child evaluations, injectivity inherited from the original cap-first tuple, and reindexing of canonical colors are all exact. Earlier-than-parent is needed in later label bounds, not in this pure ordered-list insertion identity; the source does not silently conflate those hypotheses.

**OccurrenceParent and ColoringExt.** Every nonroot occurrence has an actual parent and child slot, retaining its full dependent outer path. This comes from recursion on the finite tree, not a supplied parent oracle. Equality of outputs at every occurrence recovers the full tree coloring by product extensionality and recursion, then the paired cap and both below-root colorings. Thus recovery identifies the real summand index, rather than only an exponent histogram.

**ColorRigidity.** The induction is on the finite original vertex label. Strictly earlier children let it cancel the already recovered child sums from equal class incident sums. The explicit local lower bounds then force equality of every output in that class. Its blocker/tie corollary derives those lower bounds from a tie to an earlier label or an earlier-label blocker at every smaller canonical color. It requires exactly those shape facts and does not infer them from histogram equality. Empty occurrence classes and canonical output zero are retained.

## Remaining boundary

These eight modules provide a nonzero canonical summand and exact finite structural/recovery infrastructure. They do not themselves prove the complete canonical blocker/tie shape for every actual diagonal or edge pair, nor uniqueness of the contributing exponent or the unconditional frozen Target. Those remain separate source obligations before final independent full-target reviews and the authoritative Linux Comparator/kernel checks. IDs, canonical pages, originals and previous frozen sources were not changed by this review.

## Reviewed bytes

| Source | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP11/PriorInsertion.lean` | `db953976c47fed4c38cfcb3c00a2629fd914d7271a057dfd3a9e688ae0c7cff4` |
| `lean-statements/NLA/Proofs/SP11/AugmentedColors.lean` | `856bda135fb47417912e4ab5da092e6e4e9e44ef8c559b33ffb0202eeb5ac453` |
| `lean-statements/NLA/Proofs/SP11/CanonicalColoring.lean` | `bc1e9ea1cccf8c9805f28c7b0a5062a3fa871c7a2d1e472b8d1609c57faf9830` |
| `lean-statements/NLA/Proofs/SP11/CanonicalPair.lean` | `c93349e3f15c83b6127686fd69ad68ce5525c317b7946852c03eebe49969d37c` |
| `lean-statements/NLA/Proofs/SP11/OccurrenceParent.lean` | `0abebc9b5f6e8235ae0d845391a64254f05e5d6dc5443debd5d043739542ce1d` |
| `lean-statements/NLA/Proofs/SP11/CanonicalOutputs.lean` | `bc30ca6bea86eb1100bc983f40ad0e6c9ebd35c9121ff943f0f774ade4d73151` |
| `lean-statements/NLA/Proofs/SP11/ColorRigidity.lean` | `0454ea402344587a986a46a9e11307bd8d7e409af0b5182047dfeaa66167bc41` |
| `lean-statements/NLA/Proofs/SP11/ColoringExt.lean` | `f6780e9b7628c94cd9d3e43d1166c8f1b741b766a859c29f0b0715343c20185d` |
