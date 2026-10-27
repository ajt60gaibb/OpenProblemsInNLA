RE05 centered2 author kernel receipt
===================================

Author fresh replay PASS at 2026-10-26T23:42:41Z. Two new modules contain
17 declarations / 16 theorems in 246 lines. All 32 selected ordinary local
source files rebuilt from empty private project outputs. The separate
literal/interface/edge consumer passed all 22 explicit kernel assertions;
the deliberate `sorryAx` control was rejected. Total: 34 compiler commands.
Only the standard three axioms or subsets occur in positive checked bodies.

The exact compiler is Lean4.33.1 commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, binary SHA
`1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554`.
Pinned external package outputs were reused; project outputs were not. The
result records all ten actual external package HEADs and the exact commands.

For a Frobenius-orthogonal residual R, each literal actual same-original-plan
rhs coordinate is exactly the average centered finite quadratic

    z_j = (1/s) sum_g (g.transpose*A_j*g - trace(A_j)),
    A_j = (H E_j).transpose*(H R), E_j=orthonormalMember P j.

The actual width is proved positive at positive accuracy. The selected-left
and projected-right terms and the raw entrywise quadratic sum are all
identified exactly. Explicit lemmas prove H and A_j do not depend on the
draw or copy when P,accuracy,R are fixed. The original plan is never
regenerated on E. No mutable Gaussian source was imported.

The actual residual leverage PSD bound gives the deterministic contraction

    sum_j inner(A_j,A_j) <= threshold*inner(R,R),
    sum_j 2*trace(A_j*A_j.transpose) <= 2*threshold*inner(R,R).

Those bounds require no independence, residual orthogonality, positive
accuracy or probability premise. The matrices A_j may be nonsymmetric.
The second line is the exact deterministic charge used by a general real
quadratic variance estimate; this receipt does not claim that variance or
any Gaussian integral/tail probability.

All 18 original/model/review/registry/pin inputs and all earlier frozen
sources and anchors were checked exact before and after replay, including
regression7, one-copy4 and spectral-split5. All 217 permanent IDs and original
files remain unchanged. `ENDPOINTS.json` preserves all 16 exact theorem
headers. `AUTHOR_REVIEW.md` records the algebra, quantifiers and limits.

Source freeze:
`de22f4cd2054265fb2e2a7e1985f11798fc06a6d8b67803e282f8e6313b4aa52`.
Final source lock:
`f59edd93b9110d669c99de1271149f28b062104cc49a1332b3be53bb4b248eeb`.
Final result:
`adeb99eb90ff7f590ba78bd8d9ca61728a94ef978bf22e1856f0a0fb34ad4950`.

Reproduce with `python3 replay.py --output <new-empty-evidence-directory>`
from this evidence directory in the pinned workspace. The driver refuses
pre-existing project object outputs and checks every locked byte. Development
source and consumer elaboration failures are retained; final preflight
attempt4 passed, with reused project objects labeled as preflight only.
No fresh author failure occurred.

This is a deterministic prerequisite author replay. It makes no independent
source-approval, Gaussian moment/probability, full RE05 Target, canonical
package, Linux CI, Comparator or status-promotion claim.
