# MI-27 exact hockey-stick substitution statement review

Reviewer: /root. Scope: the eight new helper statements before bodies; no proof or run is certified here. Root authored separate inertia helpers and cannot act as a wholly nonauthor final reviewer of MI-27.

Verdict: APPROVE the exact statement packet.

The positive and negative substitutions are smooth bijections on their open domains. Their absolute Jacobians are both 1/(gamma-1)^2. Direct scalar algebra and nonnegative positive-part homogeneity give respectively E(gamma,X,Y)/gamma and E(gamma,Y,X)/gamma^2, with X,Y order preserved. The central pencil is positive semidefinite by convexity. The general improper formula retains the required trace correction; trace-one cancellation is used only in the unchanged density-matrix contract. The original supplied two-sided Loewner cutoff and R=1 case are retained. No commutativity or prior full integral identity is assumed.

Checked pinned Mathlib JacobianOneDim.lean: the two image-integrability/change-of-variable theorems accept arbitrary integrands and require measurable domain, within-derivative and injectivity, as stated in the plan. Thus the generic f headers do not silently omit a measurability premise. Bochner integrability is established separately before splitting or combining the matrix integrals.

These helper statements are consistent with the unchanged original C11 target. Implementation must still compile locally, preserve all hypotheses, and receive separate final proof reviews and actual Linux Comparator acceptance. Whole MI-27 remains incomplete.
