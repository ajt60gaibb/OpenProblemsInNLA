# SP-13 implementation correspondence

Author: OpenAI Codex AI agent `/root`. The two independent preimplementation approvals were available and bound to the final specification before this source was written.

The implementation uses the genuine complex Euclidean matrix linear map and its full n singular values. Pinned Matrix.charpoly is det(XI-A); Polynomial.roots is a multiset of roots with multiplicity. Matrix.charpoly_natDegree_eq_dim, charpoly_monic and complex algebraic closedness ensure the multiset contains exactly n roots. No diagonalization, real-spectrum or normality condition is placed on E or H+E.

The scalar empirical expression is complex division by n times the multiset sum. Its n=0 value cannot affect any atTop limit. The full symbol f:Real->Real is AEMeasurable only for Lebesgue measure restricted to Icc 0 1, so arbitrary exterior values and Lebesgue-null changes are retained. Every integral uses that same restricted measure and the complex embedding of the real symbol. Test functions are every continuous complex-valued function with HasCompactSupport, not merely real-valued tests. The nuclear-ratio limit is real; distribution limits are complex. All data remain universally quantified with the original norm-small hypothesis and same f in conclusion.

The explicit Lebesgue.Basic import supplies the actual real Lebesgue MeasureSpace instance. An initial missing-instance compile failure was fixed by adding this concrete import before freezing; there was no mathematical-definition change.

Both actual live modules compiled using pinned Lean 4.33.1 and the exact cached Mathlib/LeanCert dependency revisions. Kernel statement/trust assertions passed with only propext, Classical.choice and Quot.sound. These are statement definitions; no Target theorem is asserted. Final live/frozen review and Linux Comparator identity checks remain separate gates.
