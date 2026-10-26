# Actual minimum-error selector: frozen author replay

Author: `/root/recover_geometry`. Executed 2026-10-26T16:10:51.063950+00:00 with pinned Lean 4.33.1 (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) and LeanCert kernel mode.

The six frozen `MachineBestCandidate*` sources implement one fixed actual finite RAM program, with 30 labels, 13 natural registers and four real registers. It calls the frozen squared-error program on each stored candidate, initializes the winner on the first candidate, updates only on a literal strict real comparison and retains the previous winner on ties. Every legal trace returns a stored candidate with actual squared error no larger than every stored candidate. Memory is read-only; overlapping arrays and zero entry count are included. The candidate count must be positive. The entry contract is an actual prepared parameter-register state, with arbitrary initial best-error and scratch contents.

The exact standalone time is `(9*N+15)*K+4`; the callable endpoint returns before the local halt at `(9*N+15)*K+3`. Actual `CostThrough` is bounded by `50*(K+N+1)^2`. The arbitrary caller endpoint also preserves every register outside the injected frame.

Fresh author replay PASS: 25 project sources plus one independently expanded boundary consumer, 26 kernel commands, 44 explicit new declarations checked. No project objects were reused. Pinned external Mathlib/LeanCert caches were reused. All printed axiom sets are subsets of `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` occurs. Live and snapshotted sources, previous frozen recursive/radix sources, and all 25 original review inputs retain their locked hashes.

Source lock SHA-256: `3988bced69ed9b9cac228b1d84270185c5210cfc92ad4bcebe90ec8d5e1a8819`.
Result SHA-256: `eeacdfecb644a91d7946b216c04d3707d9a88f47cc28202ee0c62eca32a4eb14`.
Replay driver SHA-256: `9cf05f97c501e544c8ad37399d79fe08482594fcc7ae15fb8194ca23dff43246`.
Consumer SHA-256: `2713473e2507130ee4e9f2d6473a44f1d20f8975ff67718744bab0820a382287`.

Reproduce from this clone with `python3 docs/lean/proofs/TR-04/campaign-2026-10-23/best-candidate-author-2026-10-26/replay.py --output /absolute/new/output/path`; the output must have no existing project object directory. The driver snapshots and checks exact source inputs before and after all kernel commands.

This receipt is author verification of the selector component. Independent review, the complete TT program/Target, Linux CI and Comparator acceptance remain separate gates.
