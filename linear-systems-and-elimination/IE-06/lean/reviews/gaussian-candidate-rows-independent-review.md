# Independent review: fixed Gaussian candidate rows

Reviewer: infrastructure/Gaussian agent, independent of source-proof author. Verdict: APPROVED at source SHA-256 `e5b3953e06f18199c5d82ea29146861d64f7bccf383d7c475aac1404b0186450`.

All nine declarations in GaussianCandidateRows.lean were read in full. The reviewer independently rebuilt the entire 23-module local dependency closure with pinned Lean 4.33.1, before/after source hashes, and kernel trust checks. Compilation passed; the GaussianCandidateRows declarations use only propext, Classical.choice, and Quot.sound. Evidence is in `gaussian-candidate-rows-independent-compilation/receipt.json` and `compile.log`. This is local macOS kernel evidence, not Linux Comparator certification.

The inside/outside law splits the actual product Gaussian into the fixed row subset and its complement, reindexes the fixed inside subset by the explicit equivalence, restricts only to the stated first p columns, and swaps factors into outside/inside order. Each transformation is measure preserving. No pivot-dependent conditioning appears. Empty row subsets and zero-column prefixes remain valid product-space cases.

The candidate block evaluates the canonical outside-row pivot selector on the matrix restored from literal outside coordinates. Its joint measurable evaluation uses the finite outside index type correctly. The reconstruction identity uses the proved invariance of candidate labels under restoration of unchanged outside data; it therefore matches the actual fixed-candidate original rows.

The fiber lemma requires an intrinsic jointly measurable event E and a bound for every outside fiber, forms the measurable pullback through candidateBlock, and applies the actual product law followed by Tonelli. The outside measure is a probability measure, including empty-dimensional cases. It neither assumes nor constructs a measurable auxiliary nullspace frame. Such a frame may be chosen separately in each deterministic fiber only while proving the supplied bound; the integrated event itself must remain the explicitly measurable E. This is exactly the correct interface for B4 and avoids conditioning on a random next pivot set.

No defect or requested code change was found. This supporting lemma does not by itself prove the selected-block extension estimate or the overall IE-06 theorem.
