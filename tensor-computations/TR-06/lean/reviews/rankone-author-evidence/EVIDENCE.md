# TR-06 local-addition-inverse proof evidence

Implementer: `/root/tr06_statement_referee_1`, AI agent, 24 September 2026. This agent changed from pre-proof statement referee to proof implementer after both independent boundary approvals. It must not count as an independent nonauthor final reviewer of this contribution.

## Completed target

`NLA.TR06.smooth_chart_is_local_addition_inverse`, with exactly the frozen format hypotheses, SmoothDecompositionChart, point, source membership and `IsLocalAdditionInverse c u` conclusion. The unused mode-size/rank binder names have underscores, but their hypotheses remain present and unchanged. The proof actually needs only a nonempty mode index once the smooth chart is given.

Source: `NLA/TR06/RankOneCharts.lean`. It imports frozen Definitions and permitted Mathlib/LeanCert modules, never Challenge. There are no placeholders, custom axioms, native computations or added mathematical assumptions.

## Proof construction

1. At a nonzero tensor pivot, prove every factor's pivot entry is nonzero and every normalized factor is the tensor's coordinate slice divided by the pivot.
2. Prove exact Segre reconstruction `A = A(q0) • pureTensor(pivotFactors q0 A)` and absorb a scalar into an arbitrary mode.
3. Construct a genuine homeomorphism from nonzero-pivot rank-one tensors to nonzero amplitude times all off-pivot factor coordinates. Prove inverse identities, continuity, arbitrary-order smoothness of the decoder and smoothness of the rational encoder on its nonzero domain.
4. Construct the ordered product homeomorphism, prove its domains open in the WHOLE OrderedRankOne product, and prove its coordinate finrank is exactly the frozen expectedDimension.
5. Compose the reviewed smooth summand branch with the pivot encoder. Decoding and summing locally recovers the input chart; the derivative chain rule and injective input-chart differential imply injectivity of the pivot-coordinate differential. Equal finite dimensions make it invertible. Mathlib's inverse function theorem supplies an actual open local coordinate homeomorphism.
6. Compose with the pivot decoder to show the summand branch is locally an open embedding into the entire ordered rank-one product. Separately show the source smooth locus is open relative to the identifiable locus.
7. The source chart and summand branch give two open embeddings of the same coordinate neighborhood. Compose their associated open partial homeomorphisms to obtain an open partial homeomorphism from OrderedRankOne to sourceSmoothSet. Check its forward map is actual tensor summation and its inverse is the original branch on a coordinate neighborhood.

No invariance-of-domain theorem is assumed. Initial API search found no such theorem in the pinned Mathlib; the implemented inverse-function proof avoids that missing foundation.

## Actual checks

Run `python3 /private/tmp/tr06-proof-rankone/check.py` for the exact local invocation. It uses Lean 4.33.1 with the pinned package cache and an independently compiled olean of approved Definitions, SHA-256 `e5fe5314f4c17df41b5bec54f2c407b2d1eba8ba59be5d85525de13e262f8898`.

Final result: exit zero with no warnings. Eight explicit `#print axioms`/`#assert_trust kernel` pairs check the pivotal algebraic, homeomorphism, smoothness, dimension, IFT and full-target declarations. All print only `[propext, Classical.choice, Quot.sound]` and all kernel assertions pass. LeanCert is configured globally with trust `kernel`; no numerical interval certificate is needed.

Environment: Lean 4.33.1 arm64-apple-darwin24.6.0 commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`; LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`.

The earlier clean pivot-chart checkpoint remains in `checkpoints/pivot-chart/` and is explicitly superseded by the final complete local-inverse target.

## Limits

This contribution proves one required correspondence theorem, not the TR-06 integrability theorem or entire ten-declaration boundary. No Linux reproducibility or Comparator run was performed here. Integration, exact Challenge comparison and independent nonauthor proof review are still required. No frozen definitions, canonical pages, IDs, statuses or prior verifications were edited.

Final proof SHA-256: `5f79efa56be8bc3d945773d30c847aebf607a702993ed69c5d12fa56259ba5e9`.
Final typecheck log SHA-256: `3c431834e4401534918b2266e2e6de974e22103de5da0725b0aac2514a3e5d67`.
