# Independent RankOneCharts contribution review

Reviewer: `/root`, Codex AI agent. Date: 24 September 2026.
Verdict: approve integration of this contribution, not full TR-06 verification.
Reviewed source SHA-256:
`5f79efa56be8bc3d945773d30c847aebf607a702993ed69c5d12fa56259ba5e9`.

I read all 584 lines and independently elaborated a source copy in the root
proof build directory. I did not author this implementation. The exact final
target retains every frozen hypothesis and conclusion; unused binder names
have underscores, which does not change the proposition. The Definitions
module remains unchanged. Comparator has not been run.

The nonzero pivot argument is algebraically exact. Every factor pivot is
nonzero because their finite product is nonzero. Ratios of tensor slices
recover normalized factors, and the full tensor is reconstructed by one
amplitude times their outer product. Absorbing that amplitude into one mode
requires the supplied nonempty mode index; the canonical d >= 3 hypothesis
provides it. Pivot coordinates omit exactly one entry in each mode, and the
proved ordered-product finrank equals the required expectedDimension.

The coordinate encoder and decoder are actual inverse homeomorphisms on open
nonzero-pivot subsets of the entire rank-one product. Their smoothness proofs
use polynomial coordinate maps and rational divisions only where pivots are
nonzero. For a smooth decomposition chart, decoding and addition agree locally
with its input chart. Consequently the chain rule and injective input
differential imply injectivity of the encoded summand differential. The proved
equality of finite dimensions makes that differential invertible, so the
ordinary inverse function theorem supplies an open local coordinate map.

The resulting summand map is an open embedding into OrderedRankOne, not merely
into already-identifiable summands. The source smooth locus is independently
shown relatively open using the targets of its input charts. Composing the two
open embeddings gives the required open partial homeomorphism. Its forward
map is checked to be actual tensor addition throughout its source, and its
inverse agrees with the original branch on the constructed neighborhood. No
global ordered uniqueness, invariance-of-domain axiom, or unproved openness
claim is used.

Independent local Lean 4.33.1 elaboration exited zero without warnings. All
eight explicit transitive axiom closures contain only propext,
Classical.choice, and Quot.sound; all pinned LeanCert kernel assertions pass.
No placeholder, custom axiom, Challenge import, or native evaluation appears.
The source retains George Stepaniants/Caltech and Colbrook attribution.

Limits: this is local macOS development verification with cached pinned
libraries, not Linux Comparator/kernel replay. Root participated in the
statement design, so full-problem review should additionally use fresh
reviewers once all geometric and integrability obligations are proved.
