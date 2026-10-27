# IE-22 proof status

The approved target is preserved in `Challenge.lean`: exact unit row norms,
the floor `⌊theta*m⌋`, the real-matrix supremum, the Gaussian quantile and
truncated second moment, the eventual `(N,R)` uniform upper bound, the
no-smaller-constant assertion, and convergence of the supremum on every
positive high-aspect-ratio sequence. The proof constants `r`, `d`, `L`,
`delta`, all exceptional-probability and variance bounds, and the
`O_theta(n^(-1/6))` choice are recorded in `SPEC.md` as obligations.

No complete proof is claimed. The remaining work is substantial: exact
finite-dimensional singular-value/infimum infrastructure, the supremum over
all unit-row matrices, the universal projection argument, and the matching
probabilistic lower construction from IE-21. `Challenge.lean` is independent
of `Solution.lean`; the latter proves only elementary support lemmas. No
custom axiom from the challenge is imported by the solution.

The local machine has no configured elan toolchain, so no Lean, LeanCert or
Comparator command has been run. See `verification-commands.txt`.
