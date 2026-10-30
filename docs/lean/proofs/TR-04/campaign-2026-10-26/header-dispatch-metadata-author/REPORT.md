# Actual TT header dispatch and metadata writes: author kernel replay

Author `/root/recover_geometry`. Executed 2026-10-26T19:30:46.136394+00:00, pinned Lean4.33.1 commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, LeanCert kernel mode.

The two frozen modules prove actual scalar prefixes of the unchanged finite `ttProgram`, on every legal trace at arbitrary caller offset. They import the frozen assembly facts, without depending on the developing Startup module. They do not prove complete TT execution, approximation or total runtime.

`ttHeaderDispatch_steps/run_at/fields_at` start at actual running pc10 with natural97=k, k:Fin11. The literal jump and rejected tag pairs lead to the exact static handler in `2*k+3` transitions. The handler vector is `[119,144,150,157,214,222,230,295,303,311,319]`; its entries match the controller JSON startup/first-mode/first-cols/first-rank/child-mode/child-cols/child-rank/reverse-rows/reverse-rank/reverse-cols/reverse-stride names. Memory and all real registers remain unchanged; natural123 becomes k and every other natural register is preserved. The proof composes two-step reject blocks and the final actual compare, rather than assuming a dispatch evaluator. The trace's actual `CostThrough` increases by at most `2*k+3`.

`ttMetadata_steps/run_at/fields_at` start at running pc241 with actual natural68=L.metadata, natural125=4 and natural84=level. Two literal multiply/add instructions compute the pointer. Four actual three-step cast/write/increment blocks store the casts of original natural85/86/87/88 at metadata+4*level+[0,1,2,3]. After exactly14 transitions pc255 is running and pointer93 is metadata+4*level+4. Every address outside that four-cell block is preserved, as are all natural registers except93 and all real registers except13. No shape positivity, dimension cap or precomputed metadata value is assumed. The finite-prefix memory is a proved poststate of the actual instructions. Actual `CostThrough` increases by at most14.

Fresh author replay PASS:39 project closure sources plus one literal boundary consumer,40 kernel commands. All38 public explicit definitions/theorems plus the named local finite-real-register positivity instance are asserted in kernel mode; printed axiom sets are subsets of `propext`, `Classical.choice`, `Quot.sound` and contain no sorry axiom. No project objects were reused. Pinned external package caches are reused. No warnings occur in the two new sources. The consumer expands all11 handler addresses, checks literal tag0/time3 and tag10/time23, and states the actual four cells, preservation and charged bounds explicitly.

All live/snapshot source hashes, frozen root assembly code/generator/layout, prior dimension/layout/selector/radix support, runtime/statement pins and all25 original review inputs pass preservation checks before and after replay. Development probes explicitly reused root author objects; they are separate from this complete fresh acceptance replay.

Source lock SHA-256: `232f378a6fc5ce0cbbf62b6a2bd22a4a0cf843c3ec33af4c17763af773722069`.
Result SHA-256: `cab9bd18b4f62c5d0ce72f961710e8d0c0eeb541b1cf581144d9351a8821b822`.
Replay driver SHA-256: `f85c3321db3546f17b39a8599184e83dbac297e815ce968418c07252c53a716e`.
Consumer SHA-256: `d50afac92c01c447148dba36ca962467d34b9449c421155a1ea6a59fd3836854`.

Reproduce from this clone with `python3 docs/lean/proofs/TR-04/campaign-2026-10-26/header-dispatch-metadata-author/replay.py --output /absolute/new/output/path`. The output must not contain project objects. Only source-locked inputs and pinned external dependencies are used.

This receipt is author verification, with no independent replay/review, complete literal Target, Linux CI or Comparator acceptance claim.
