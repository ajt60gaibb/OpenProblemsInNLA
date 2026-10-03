# Proper identifiable immersion: completed conditional analytic contribution

The exact three independently approved proposition statements are proved without changes. RegularChartDefinitions.lean is byte-identical to RegularChartBoundary.lean and evidence/approved-boundary.lean, SHA256 c26acc35698f1178aafc068b9da7c8d25f28fba50eabd2d51714267ee4ad93b7. Root's pre-proof approval is preserved in evidence/root-boundary-review.md. No proof body imports Challenge, and no frozen definition, target, problem ID, or attribution was edited.

## Proven statements

1. `addition_fiber_neighborhood : AdditionFiberNeighborhoodStatement`. Full closed-product compactness gives a compact preimage T of a small target closed ball. Extend the open ordered-rank-one neighborhood to an ambient open W. The sum image of T\W is compact/closed and avoids A: exact rank removes zero summands from every closed-product fiber tuple, and the specified full fiber is contained in W. A sufficiently small ball avoids that image. This controls all nearby actual ordered decompositions, including potential distant branches.
2. `smooth_chart_of_proper_immersion : SmoothChartOfProperImmersionStatement`. A continuous linear left inverse of the actual pivotSum derivative makes a square local map with invertible derivative. The C1 inverse function theorem supplies an injective open parameter patch; derivative injectivity remains open. The genuine pivot decoder embeds that patch openly in the entire ordered rank-one product. Properness plus actual identifiability proves that the image under addition of every such open patch is open in the whole identifiable set: saturate by all finite permutations, apply the preceding neighborhood lemma, and undo a permutation using invariance of the sum. Continuity, injectivity and this open-map property construct the actual open partial homeomorphism. A continuous linear equivalence transports the complete pivot parameter space to EuclideanSpace of exactly expectedDimension. Its smooth polynomial input and summands, nonzero-normalized smooth output, and injective derivative give every frozen SmoothDecompositionChart field. The base ordered summands equal the specified decoded tuple exactly; the whole image lies in U.
3. `smooth_regular_on_proper_immersion : SmoothRegularOnProperImmersionStatement`. For each actual identifiable tensor in U, choose a real decomposition and nonzero pivots, reconstruct the exact tuple, and invoke statement 2 with the given immersion certificate. Its conclusion is precisely U intersect identifiableRealSet subset smoothRegularSet.

These results retain r=0 and degenerate mode dimensions. Only the last two require d>0 for the actual amplitude-absorbing decoder. No freeness of the permutation action is assumed. Ordinary product parameter norms are related to Euclidean coordinates by a smooth linear equivalence; no unproved isometry or volume identity is used. The inverse function theorem is used only for the local injectivity patch; smoothness of the actual chart input/summands follows directly from their polynomial parameterization, so a separate smooth inverse theorem is unnecessary for these frozen fields.

## Verification

Each final source and the consolidated audit rebuilt locally with Lean 4.33.1 arm64-apple-darwin24.6.0, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Mathlib 0df444a360eaa60ab8c11dca51a86af692955474; LeanCert 621a43d7cf21f87872392a01e874f2f1dbddc926. All seven module exits are 0 and current logs have no warnings. The consolidated RegularChartAudit checks assignability to each approved statement and prints all ten theorem/lemma closures: exactly [propext, Classical.choice, Quot.sound] for each. All ten `#assert_trust kernel` assertions pass. Source scan found no sorry/admit/custom axiom/native_decide/implemented_by/extern/unsafe occurrence. No numerical computation is needed.

EVIDENCE.json records source/olean hashes and exact imported dependency hashes/paths. Per-file logs and receipts with commands and timestamps are preserved under evidence/. check.py is the actual local runner. Compilation order is RegularChartDefinitions, AdditionNoEscape, AdditionOpen and ImmersionPatch, PivotChart, RegularChart, RegularChartAudit. The imported frozen Definitions, independently reviewed ClosedFibers and previously reviewed RankOneCharts oleans are reused; no claim of rebuilding those dependencies in this contribution is made.

| Module | SHA256 |
| --- | --- |
| RegularChartDefinitions | `c26acc35698f1178aafc068b9da7c8d25f28fba50eabd2d51714267ee4ad93b7` |
| AdditionNoEscape | `8315cc9532e99a9d25e27ea7dd04964a9e06ecb79063b22acba32d9ffeb891a1` |
| AdditionOpen | `46c3cae15976bcb4f526b8570a5a3addb5c9210917fd006c778b6dcd27b3ab32` |
| ImmersionPatch | `db80fa4f6e5d3360a595ecc48b8cb0bf946589a162df61f7ff87c68b387ea887` |
| PivotChart | `43cbbcdb24ad6bf2d7dbbff062b420e5153a9eb4cbda2416af4dea4ec9f2b92e` |
| RegularChart | `b425a6a64b9d6e52bc8272d02c8978fd1b6ff03f97683dc0dd91f810eba3710a` |
| RegularChartAudit | `d14343e921cfa5fec300675d4177022782c15336920a8f06f2101ac66c318c66` |

## Limits

This proves conditional analytic bridges with explicitly intermediate open-set identifiability, complete relative properness, and actual Segre derivative hypotheses. Those hypotheses still must be derived from the original genericity assumption. This contribution does not assert generic algebraic localization, full smooth-locus measure, positive volume, finite angular mean, completed Comparator correspondence, Linux CI success, or full TR-06 verification. Status promotion and a fully verified PR remain root-level obligations after all target proofs and independent final review.

Authors and original mathematical attribution are retained: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology; original TR-06 mathematical proof by Matthew J. Colbrook. No contact email was added.
