# TR-17 pre-implementation specification: independent review

**Verdict: APPROVE.** Reviewer: `/root/inventory_review`, 2026-10-09. This approval concerns fidelity of the statement specification, not a Lean implementation or a new proof of the source theorem.

I compared the complete canonical README, its byte-preserving `ORIGINAL.md` copy, and the resolution manuscript's Theorem 1 and metric convention. The specification retains every permitted Segre–Veronese format (`k≥1`, factor dimensions at least two, positive symmetric degrees totaling at least three), the full scalar rank-one complex cone, and its smooth nonzero part for critical-point counting. It distinguishes the real tensor space from its complexification, requires complex-*bilinear* extension of every positive definite symmetric real metric, and counts Zariski-generic complex critical points with algebraic multiplicity. It identifies the Frobenius metric as the restriction from the full tensor product, including repeated-entry weights. The exact inequality is required for *every* positive definite metric with no generic-metric or reduced-fiber premise. I found no omitted case, changed metric, or weakened degree count.

| Input | SHA-256 |
| --- | --- |
| `tensor-computations/TR-17/README.md` | `d5fd05e1116e654027debc79f16c432f3b02a3034d52a7b54247ea788f63c3ca` |
| `docs/lean/statements/TR-17/ORIGINAL.md` | `d5fd05e1116e654027debc79f16c432f3b02a3034d52a7b54247ea788f63c3ca` |
| `docs/lean/statements/TR-17/NUMERICAL_TARGETS.md` | `08d4027ca2d185945da636498173fb90fcec4d5d565a22a839090ea6c94eb120` |
| `references/colbrook-tensor-metrics-rank-2026-09-11/manuscripts/tr17_solution.tex` | `abbaff0249f941e745810173e425b6ce424a0915066088ebdba8f6fc5e9548cb` |
