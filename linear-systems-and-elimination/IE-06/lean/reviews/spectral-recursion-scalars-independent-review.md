# Independent exact-code review: spectral recursion scalars

Reviewer: /root/independent_math_review. Approved the entire frozen
NLA/IE06/SpectralRecursionScalars.lean, SHA-256
`aa697fe69825580c97f2db7f56f3e50ac689ed02485b5a9be9854369117d6bb2`.
Reviewed every proof against spectral-recursion-specification.md and the
unchanged ScalarRecurrence definitions. No mathematical issue was found.

Nonnegative cost and its first-term lower bound are proved from the actual
finite sum/recurrence. The profile upper bound is d/sqrt(n). Strict d<n and
d>0 give profile(d)<sqrt(d), exactly preserving the strict B4 mu hypothesis.
The exponential baseTheta is positive, and at most one for D>=4 and ell>=0.
The threshold comparison uses cost>=1+ell/d and 4e<=exp(4); the latter follows
symbolically from exp(3)>=4. The scale replacement sqrt(n) by sqrt(t) is in
the correct direction under t<=n, with positive denominators justified.

The base dimension estimate t*ell<=8d^2+800d*ell uses the literal step ceiling
bound, not a rounded or altered recurrence. With D>=4beta+4004, the negative
coefficient (D-4)/4 is at least beta+1000. The positive exponent is at most
8d^2+(beta+802)d*ell, leaving the nonnegative surplus
(beta+992)d^2+198d*ell. Thus the exact n^t * t^(d+1) * theta^(d^2/4)
prefactor is absorbed into exp(-beta log n); natural and real powers are
handled explicitly. No probability factor was dropped or giant threshold
numerically evaluated.

The recursive profile inequality uses D>=100C and C>=0, together with
1+step*ell/d^2<=2+100ell/d. Multiplying 1+ell/d by 100 dominates this loss,
with a safe constant surplus; the exact profile recurrence supplies the
remaining d/step prefactor. All inverse comparisons have positive dimensions
or step. Finally ell>=256 gives ceil(sqrt(ell))>=16 symbolically. This module
proves deterministic scalar support only; it does not claim the eventual
unconditional Gaussian recursion or the manuscript's sharper arbitrary-r
log-log intermediate estimate.

Independently recompiled the unchanged source with pinned Lean 4.33.1 in a
private build using existing pinned dependency caches. All 14 local kernel
assertions and printed axiom audits passed with only propext, Classical.choice,
and Quot.sound; no warnings occurred. Source hashes were unchanged before and
after compilation. Receipt/log are in reviews/spectral-recursion-scalars-independent/.
This is not a fresh dependency rebuild or cached-proof replay. No source was
edited by the reviewer.
