# Concrete TT memory layout: frozen author replay

Author `/root/recover_geometry`, executed 2026-10-26T18:38:08.954866+00:00. Pinned Lean 4.33.1 commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; LeanCert kernel mode.

Four frozen modules implement the exact requested natural address allocation, starting at original input data base `B=2*d-1` and entry count `N`. They reserve three N² SVD squares, two N sigma arrays, d N² frame blocks, four metadata cells per level, two N-cell dense work buffers and K N-cell stored candidates. The precise exclusive end is `B+(d+3)*N²+(K+5)*N+4*d`. For original shapes and `K≤N+1`, every allocated address is below `20*(Size+1)^3`.

Theorems prove the literal machine `OutputBlocksDisjoint` for first and child SVDs whenever both dimensions are ≤N. Distinct level frames, work buffers, metadata cells and candidates have exact block/field separation. Actual first SVD writes preserve the input prefix and all regions after its three outputs; actual child SVD writes preserve all work/candidate addresses and every other frame. Generic block containment transfers reservation disjointness to actual rectangles. Frames fit N² using separate dimension bounds; an N-cell dense work buffer requires its explicit rectangular product bound. Actual strided contraction/lifting `MatrixMultiplyData` records have proved input/output safety and exact readMatrix/transpose meanings. No recursive product invariant is assumed as a theorem here.

Final fresh author replay PASS: nine project sources plus expanded literal consumer, ten commands; all 88 explicit authored declarations checked, standard three axioms only, no project object reuse. Pinned external package caches are reused. The consumer expands first/child output addresses and original total heap expression, checks zero dimensions, and retains explicit dense-work product premises. All locked live and snapshot inputs, prior selector/radix/recursive sources and 25 original review inputs are unchanged.

Source lock SHA-256: `e6b0ca4835dcdac42dea4a820dca3dddfae658f4b52390d00972984a9cad7de3`.
Result SHA-256: `2e56fb5d73de932c6c115b67ca67b90cb0262459150ba12f9efdfc9098a69aa9`.
Replay driver SHA-256: `9fa3c87b45ad15633881edd57f50d8b4b1edfaa777c1f7abaff7e2b8c7249a3a`.
Consumer SHA-256: `6bce86d1eba3922035a1a4513b00158f91527dca6db4bac605eee3241f855d8f`.

Reproduce with `python3 docs/lean/proofs/TR-04/campaign-2026-10-23/tt-memory-layout-author-2026-10-26/replay.py --output /absolute/new/output/path` in this clone. The output must not contain project objects.

The superseded warning-cleanup lock and failed initial replay remain under `source-lock-superseded-cleanup.json` and `run/`. That attempt exposed an unconstrained implicit address after deleting an apparently redundant `change`; final frozen Matrix uses an explicit address argument. Acceptance is exclusively the final fresh replay under the lock above. The initial diagnostic did not change any older frozen component or model.

This is author evidence for allocation/safety/address bounds. It does not claim independent review, a complete TT program or literal Target, Linux CI or Comparator acceptance.
