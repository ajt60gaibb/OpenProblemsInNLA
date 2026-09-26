# Independent contribution review: finite complete fibers force exact rank

**APPROVE** the exact contribution, with no requested source changes:

- FiniteFiberExactnessBoundary.lean SHA256 `96b4045af8b02e01d235849609f523437ee84f30cfb0e2dc5f6614b2b5babc51`.
- FiniteFiberExactness.lean SHA256 `eeae8de29b1390c7ee63f9b43913a3e489bd3934ceeeb0cb78deb6ce9f834a9a`.

Reviewer: `/root/tr06_statement_referee_2`, not author of either source or the imported scalar-absorption lemma. I independently read the entire boundary, implementation, plan, root pre-proof approval, relevant original ClosedFibers definitions/zero-removal lemma and Segre.pureTensor_smul_mode. The boundary is byte-identical to the root-approved snapshot; all six proposition definitions and the three fixed tuple constructions are preserved. Current original source hashes still match the copied review bytes. No source files were changed.

## Mathematical review

The final conclusion is exactly the frozen `ExactRank r A`: existence of an actual length-r rank-one decomposition and exclusion of every shorter such decomposition. Its premises are finiteness AND nonemptiness of the COMPLETE existing closedAdditionFiber, with d>0, positive mode sizes, and r≥2. It supplies no identifiability premise and uses actual Set.Finite/Set.Infinite throughout, avoiding the zero-value convention of Nat.card for infinite sets.

The initial rank bound removes every zero entry of any chosen tuple from a nonempty complete fiber, retaining its sum and obtaining an actual decomposition of length m≤r. It imposes no unnecessary format restrictions and covers empty tuples.

For positive shorter length m, the fixed splitTuple places t*a0 and (1-t)*a0 in positions 0 and 1, then retains a1 through a(m-1) exactly once and pads only the remaining positions with zero. I checked the Fin-index arithmetic in sum_splitTuple: after writing m as successor and r as m+1+k, the two head entries and shifted remaining block account for the entire original sum, and all k tail entries are zero. The first output coordinate determines t because a0 is genuinely nonzero. Scalar multiples remain zero or rank one by absorption into an actual mode. t=0 and t=1 are retained in the complete fiber; no nonzero-scalar restriction is hidden.

For m=0, the empty decomposition forces A=0. Positive mode sizes give an actual coordinate of the all-ones pure tensor, whose value is 1, so it is genuinely nonzero. The explicitly fixed cancelTuple contains t*B, -(t*B), and zeros; its first coordinate is injective in t, and its sum is 0. The proof applies infinitude of the RCLike scalar field to the injective ranges in both branches, yielding genuine Set.Infinite fibers.

The exact-rank theorem first rules out m<r for the decomposition provided by zero removal, giving m=r; it then separately excludes every hypothetical shorter decomposition by the same infinite-fiber contradiction. The nonempty hypothesis is used and preserved. d>0 is required for scalar absorption; r≥2 is required for the cancellation construction; positive mode sizes are required to provide its nonzero tensor. Omitting these would admit counterexamples, and the code does not do so. The unit-tensor lemma alone correctly also permits d=0 because its empty product is1.

## Independent kernel rebuild

Copied sources were rebuilt in this isolated directory, with NO original contribution oleans in LEAN_PATH. All seven local modules were rebuilt from source in dependency order: frozen Definitions, Complexification, ClosedFibers, SegreBoundary, SegreCoordinates, FiniteFiberExactnessBoundary, FiniteFiberExactness. Each exited 0 without warnings. The review-only Audit.lean then checked assignability of each advertised theorem to its exact approved proposition and audited all 11 new theorem closures plus the used Segre scalar-absorption lemma. All 12 closures are exactly `[propext, Classical.choice, Quot.sound]`; all 12 LeanCert kernel assertions passed. Audit also exited 0 without warnings.

Pinned versions: Lean 4.33.1 arm64-apple-darwin; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`; LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. Exact copied bytes, logs, per-file commands/timestamps/status receipts, check.py, source-hashes.json and REVIEW-EVIDENCE.json are retained here. The source scan found no sorry/admit/custom axiom/native_decide/unsafe/implemented_by/extern mechanism in either reviewed contribution source. The extra audit is verification evidence only, not a new production proof module.

## Scope and presentation

This approval permits including the contribution as verified supporting mathematics in the authorized INCOMPLETE draft PR. It does not establish that any intended localized fiber is finite/nonempty, generic identifiability, real/complex rank equality, properness, derivative injectivity, smooth-locus correspondence, finite angular mean, successful full-target Comparator/CI, or complete TR-06 verification. No promotion to Lean verified is justified. The proof retains George Stepaniants's name, Department of Computing and Mathematical Sciences, California Institute of Technology affiliation, and original proof attribution to Matthew J. Colbrook, with no contact email.
