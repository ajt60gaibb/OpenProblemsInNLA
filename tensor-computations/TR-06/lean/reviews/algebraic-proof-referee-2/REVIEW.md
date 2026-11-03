# Independent review of complexification and full closed fibers

Reviewer: `/root/tr06_statement_referee_2`, independent of the contribution author. Verdict: **APPROVE at the inspected hashes below**. No mathematical or trust change is requested; no candidate source was edited.

| Module | Inspected and rebuilt SHA-256 |
| --- | --- |
| Complexification | `450fab69ba73e4dbfa5b1ec9667d76cf1ebf1670caa1ec9e6edaec5d43a8c164` |
| ClosedFibers | `d811691726c5f8851b9a8d3ff8016cbba5794ac5e1e90b2d7e80507489383663` |

I compared both modules with the root-approved `STATEMENT_PLAN.md` (SHA-256 `71f50263e30c5098ddd490efd82d76febe7704a1e803369ef9e5840b1bb0986f`), frozen Definitions, and final evidence. The implemented boundaries match those records and do not replace a frozen TR-06 target.

## Complexification

`complexify` is literally coordinatewise real inclusion into complex coordinates. Coordinate equality and Complex.ofReal injectivity prove it injective. Its zero, addition, finite-sum, and pure-tensor identities follow the actual coordinate products and sums. Nonzero real rank-one tensors remain nonzero complex rank-one tensors because factor witnesses are mapped coordinatewise and zero is reflected by injectivity. Thus every actual real decomposition gives the corresponding actual complex decomposition.

`exactRank_of_complexify` deliberately requires **a supplied real length-r decomposition** as well as complex exact rank r. It uses that supplied witness for real existence; any shorter real decomposition would map to a forbidden shorter complex one. It makes no universal real/complex rank-equality claim and does not infer real decomposability from complex decomposability. `identifiable_of_complexify` applies complex uniqueness to the images of two actual real decompositions and reflects equality under the same finite permutation. The combined theorem has precisely these conditional meanings. No genericity, positive-volume, smoothness, or witness outside an algebraic exceptional set is manufactured.

## Full closed-product fiber

`rankAtMostOne A` is exactly `A=0 ∨ RankOne A`; `closedRankOneProduct` includes every tuple whose summands satisfy that predicate; `closedAdditionFiber` imposes only that complete product membership and the actual sum equation. It does not prescreen zero entries, select a chart, quotient by permutations, or use factor vectors with scaling gauges. The word closed is a candidate description only: the definition and documentation explicitly leave topological closedness as a separate proof obligation.

`exists_decomposes_remove_zeros` indexes **exactly every nonzero position** by a finite subtype, reindexes it by Fin m, and proves the resulting sum equals the original full sum because the omitted positions sum to zero. Each retained position has genuine nonzero RankOne status. The subtype cardinal is at most r and strictly smaller whenever any original position is zero; it makes no incorrect claim that an arbitrary subset or one selected nonzero position retains the sum.

For an exact-rank-r tensor, a zero entry anywhere in its complete closed-product fiber would therefore produce a strictly shorter genuine decomposition of the same tensor, contradicting frozen ExactRank. Every fiber tuple is consequently a genuine length-r decomposition. Fixing a decomposition supplied by exact rank, identifiability puts every full fiber tuple into its finite permutation orbit. Subset finiteness proves finiteness of the **entire actual tensor-tuple fiber**, and the same fixed decomposition witnesses nonemptiness. No alleged converse or uniform cardinality bound is used.

All statements retain arbitrary d,n,r and RCLike scalar fields where declared. For r=0 the tuple type has its unique empty function, the nonzero-position subtype is empty, and the strict-decrease premise has no witness; exact rank zero provides the zero-sum identity. The final fiber is the expected nonempty singleton under the stated rank hypothesis, so no positive-rank or nonempty-index assumption is hidden. Degenerate mode sizes and d=0 remain governed by the actual frozen predicates rather than a substitute geometric cone.

## Independent rebuild and trust

Both source hashes matched the final author manifest before copying them into this isolated review directory. I rebuilt both snapshots afresh with pinned Lean 4.33.1, pinned Mathlib, pinned LeanCert, and the immutable frozen Definitions object. Both exited 0 with no warnings or errors, and their existing central kernel assertions passed.

A supplemental `ExportAudit.lean` checks all 18 public definitions/theorems, including elementary complexification operations and closed-product definitions. Every transitive axiom closure reports only `propext`, `Classical.choice`, and `Quot.sound`, and all 18 `#assert_trust kernel` checks passed. No Challenge import, custom axioms, sorry/admit, native computation, or claimed genericity conclusion is present. Source snapshots, commands/environment, dependency-object hashes, timestamps and logs are retained under `evidence/`, together with exact review runners.

These results are elementary supporting foundations. They do not prove the cone is topologically/algebraically closed, a polynomial-minor characterization, infinite shorter-rank fibers, generic finiteness, regularity of addition, or full TR-06. No Linux Comparator replay or full-target verification is claimed. Both source headers preserve George Stepaniants's name, Department of Computing and Mathematical Sciences, California Institute of Technology, and original mathematical proof attribution to Matthew J. Colbrook, with no contact email.
