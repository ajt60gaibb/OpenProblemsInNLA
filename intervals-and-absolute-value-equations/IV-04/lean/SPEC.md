# IV-04 statement specification

Source correspondence: `04_twenty_problem_resolutions/main.tex`, section
`sec:intervals`, theorem `thm:iv-hull`; canonical source snapshot
`sources/aa8d010bdd5a/intervals-and-absolute-value-equations/IV-04/README.md`.

## Canonical computational target

The input is an `n x n` real tridiagonal interval matrix family `T`, `n >= 1`,
and an interval vector `b`, all with rational endpoints. All remaining matrix
entries and vector entries vary independently; intervals may cross zero and
singular matrices are allowed. Define the united solution set

`Sigma(T,b) = { x : exists A in T, exists y in b, A*x=y }`.

The exact coordinatewise hull must report the empty set when appropriate;
otherwise, for every `i=1,...,n`, it returns
`[inf_{x in Sigma} x_i, sup_{x in Sigma} x_i]`, with infinite endpoints
explicitly represented and finite endpoints returned exactly as rationals.
The original question asks for deterministic polynomial time in total binary
input length.

The paper's negative result is NP-hardness of exact hull computation even for
regular independent-entry tridiagonal families, point right-hand side
`b=-e_N`, fixed superdiagonal entries all equal to `1`, nonempty bounded
solution sets, and matrices that are nonsingular throughout the family. A
polynomial-time exact algorithm would imply `P=NP`; the paper does not claim
an unconditional separation.

## Reduction and constants

Use the same PARTITION construction as IV-02, with positive weights, `W`,
`delta=1/(10*W^2)`, `t_i`, `c_i`, `s_i`, `theta_i`, and even dimension
`N=4*m-2`. Every determinant is positive, so every matrix is regular. The
corner-cofactor identity for superdiagonal entries equal to `1` is
`(T^{-1})_(1,N) = (-1)^(N+1)/det(T)`. Since `N` is even and `b=-e_N`,
the first solution coordinate is `x_1=1/det(T)>0`, and its lower hull endpoint
is exactly `1/(max_q det(T(q)))`. Comparing it with `1/tau`, where
`tau=1-delta^2/2`, decides the IV-02 threshold and transfers NP-hardness.

The full output convention also includes empty/unbounded cases and the paper's
`FP^NP` exact-output upper bound via orthant polyhedra, rational feasibility,
recession certificates, binary search, and bounded-denominator rational
recovery. These are retained in scope rather than silently replaced by the
regular bounded special case.
