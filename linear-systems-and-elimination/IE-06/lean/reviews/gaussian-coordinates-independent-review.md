# Independent exact-code review: Gaussian coordinate reconstruction

Reviewer: /root/independent_math_review. Approved frozen source SHA-256
`457bb968a1b3aac5286d169017d774a504d88a54e87acce375cf868115d47869` after reading every definition and proof. The source matches the
previously approved exact column-split coordinate contract.

The fixed embedding pi partitions original prefix coordinates into selected
and remaining rows. restore's chosen index depends only on membership in the
fixed range of pi; injectivity identifies it uniquely. Each prefix and future
coordinate is restored exactly, and the inverse identities prove no row or
column information is omitted. Measurability is entrywise with fixed branch
conditions. The selectedRows invariance is the actual previously proved
canonical-prefix dependence and adds no adaptive-law assumption.

futureIndex sends offset j to the original column label t+j and subtracts t
in its inverse, hence is the increasing suffix bijection. denseFuture swaps
the outer future-column index into standard row-major rectangular coordinates;
its pushforward is derived from the finite Gaussian reindex law and the actual
Gaussian transpose law. indexedFuture's reverse pushforward follows from the
proved inverse and measurable map composition. Thus both laws are genuine
coordinate pushforwards, including t=n and other empty dimensions; they do
not assert independence after conditioning on a success event.

Independently compiled the unchanged source under pinned Lean 4.33.1 in the
reviewer's private build. All 17 local LeanCert kernel assertions passed, all
four printed main results use only propext, Classical.choice and Quot.sound,
and there were no warnings. Current RightInverseBounds and GaussianColumnSplit
imports were also recompiled as needed for this build. Existing pinned-package
and other local dependency caches were used; this is not a fresh dependency
rebuild or kernel replay of cached objects. Hash and full coordinate-module
log are retained in reviews/gaussian-coordinates-independent/. No mathematical
or other source file was edited by the reviewer.
