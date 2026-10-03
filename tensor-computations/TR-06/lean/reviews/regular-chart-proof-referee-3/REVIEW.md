# Independent RegularChart contribution review

**Decision: APPROVE for the explicitly incomplete partial TR-06 PR.**

Reviewer: infrastructure/area subagent. I did not author these seven contribution files or their pre-proof boundary. I independently read every contribution proof, the approved boundary and root pre-proof review, the frozen chart/rank/identifiability definitions, and the directly used ClosedFibers and RankOneCharts APIs. I rebuilt all ten project modules from source into a fresh isolated directory. No project `.olean` was reused. Pinned Mathlib and LeanCert dependency caches were reused; this is not Linux Comparator execution or a fresh dependency rebuild.

## Statement and proof correspondence

The three approved propositions are unchanged. RegularChartDefinitions, RegularChartBoundary, and evidence/approved-boundary are byte-identical at `c26acc35698f1178aafc068b9da7c8d25f28fba50eabd2d51714267ee4ad93b7`. Frozen canonical Definitions is exactly `e5fe5314f4c17df41b5bec54f2c407b2d1eba8ba59be5d85525de13e262f8898`. The delivered audit is named RegularChartAudit, not TrustAudit; it checks exact assignability to all three approved propositions and the axiom closures/trust of all ten substantive exports.

- AdditionNoEscape uses compactness of the complete zero-inclusive closed-cone preimage of a small closed ball. The compact sum image of the complement of an ambient open extension avoids the base point because exact rank excludes zero summands in every limiting fiber. Thus it controls all nearby ordered decompositions, with no selected-branch compactness premise.
- AdditionOpen saturates an open decomposition set by permutations, uses actual uniqueness for every base fiber, and applies no escape to prove openness relative to the entire identifiableRealSet. It does not assume the desired target openness or require a free permutation action.
- ImmersionPatch uses a continuous left inverse of the injective derivative, the square inverse function theorem, and openness of derivative injectivity. It asserts local injectivity of the original map without claiming ambient openness of its image.
- PivotChart combines the actual decoder open embedding with the proved relative open-map property of addition; it constructs the required open partial homeomorphism into the full identifiable subtype.
- RegularChart transports the exact pivot-space dimension to EuclideanSpace using a continuous linear equivalence, proves all frozen smooth input/summand/normalized-output fields, proves derivative injectivity using local equality on the open source, retains the specified ordered branch, and keeps the entire chart image in U. Its final assembly chooses actual pivots from a nonzero rank-r decomposition.

The r=0 case remains covered by the exact quantifiers; nonzero-mode impossibility is not bypassed. The d>0 condition is used only to obtain a real tensor mode for the amplitude-absorbing decoder. No chart-source smoothness or target-openness hypothesis was added; those are conclusions/constructed fields. No isometry or volume theorem is inferred from the arbitrary finite-dimensional coordinate equivalence.

## Fresh reproduction and trust

To reproduce, copy `rebuild.py` into a fresh empty review directory and run it there; it deliberately refuses reuse of an existing project object file. The complete command/environment/source hash/exit/output object hash for each of ten modules appears in receipt.json, with full logs under logs/. All ten exits are zero, with no warnings. RegularChartAudit prints exactly `[propext, Classical.choice, Quot.sound]` for all ten exports, and all ten LeanCert `#assert_trust kernel` assertions pass. The contribution and these three project dependencies contain no occurrence of sorry/admit/custom-axiom/native_decide/implemented_by/extern/unsafe. This scan is not a claim about the separate incomplete Challenge specifications.

| Module | Source SHA256 |
| --- | --- |
| Definitions | `e5fe5314f4c17df41b5bec54f2c407b2d1eba8ba59be5d85525de13e262f8898` |
| ClosedFibers | `d811691726c5f8851b9a8d3ff8016cbba5794ac5e1e90b2d7e80507489383663` |
| RankOneCharts | `5f79efa56be8bc3d945773d30c847aebf607a702993ed69c5d12fa56259ba5e9` |
| RegularChartDefinitions | `c26acc35698f1178aafc068b9da7c8d25f28fba50eabd2d51714267ee4ad93b7` |
| AdditionNoEscape | `8315cc9532e99a9d25e27ea7dd04964a9e06ecb79063b22acba32d9ffeb891a1` |
| AdditionOpen | `46c3cae15976bcb4f526b8570a5a3addb5c9210917fd006c778b6dcd27b3ab32` |
| ImmersionPatch | `db80fa4f6e5d3360a595ecc48b8cb0bf946589a162df61f7ff87c68b387ea887` |
| PivotChart | `43cbbcdb24ad6bf2d7dbbff062b420e5153a9eb4cbda2416af4dea4ec9f2b92e` |
| RegularChart | `b425a6a64b9d6e52bc8272d02c8978fd1b6ff03f97683dc0dd91f810eba3710a` |
| RegularChartAudit | `d14343e921cfa5fec300675d4177022782c15336920a8f06f2101ac66c318c66` |

## Publication scope and infrastructure notes

These are conditional analytic supporting results. Identifiability on U, complete relative properness, and actual Segre derivative injectivity are still premises to be supplied from original genericity. Approval does not establish regular-locus full measure, positive/finite volume, angular integrability, a complete canonical target, or source-to-target numerical correspondence. The canonical status must remain Solved; no Lean-verified promotion follows.

Known release points from the current worktree snapshot: the pinned lakefile still defaults to Solution while there is no Solution.lean, so ordinary completed-project build/verify gates are intentionally unmet. The retained development_proofs.py accepts explicit compiler/cache paths and is the appropriate local-development command; the author-local check.py alone is machine-specific. No Linux Comparator run/control execution was performed by this review. Existing metadata correctly says incomplete/not-run, but its supporting-progress and review prose still says thirty-two modules while new modules are being added; update those counts/descriptions before publication and list these three results as supporting conditional lemmas. All original proof attribution and George Stepaniants/Caltech credit are present; no contact email appears.
