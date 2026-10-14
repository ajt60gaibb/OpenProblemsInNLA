# MF-23 pinned proof source and license

The 41 files under `OAI/Analysis/DirectCrouzeix/` are byte-identical copies
of the transitive Lean import closure of `CompleteBound.lean` at
[`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/DirectCrouzeix).
The upstream directory's Git tree is
`5374ca34f6707460b2d2a3eb98b1ae7af6ea25ff`; `Main.lean` is the
one directory module outside this import closure. `Sharpness.lean` remains
because `CircleFourier.lean` imports it, though MF-23 selects only the
`complete_crouzeix` theorem. All copied file hashes are listed in
`upstream-source-lock.json` and checked before verification.

The pinned upstream repository publishes its source under the
**Apache License, Version 2.0 (SPDX-License-Identifier: Apache-2.0)**.
The exact upstream root license text is copied here as
`UPSTREAM-LICENSE.txt`. The upstream formalization contributors retain
their credit; this project's `CanonicalStatement.lean`,
`CanonicalBridge.lean`, `Challenge.lean`, and `Solution.lean` are local
adaptation files. The adaptation does not imply upstream endorsement.

The canonical MF-23 target and independent pre-proof statement review are
documented in `docs/lean/proofs/MF-23/` at the repository root. The original
problem page and permanent ID are unchanged.
