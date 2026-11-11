# IE-22 statement specification

Source correspondence: `04_twenty_problem_resolutions/main.tex`, section
`sec:rows`, theorem `thm:row-universal`; canonical source snapshot
`sources/aa8d010bdd5a/linear-systems-and-elimination/IE-22/README.md`.

## Canonical target

Fix `0 < theta < 1`. For every positive integer `m,n` and every real
`m x n` matrix `A` whose rows have Euclidean norm one, define `s_theta(A)` as
in IE-21, retaining `floor(theta*m)` rows. Define

`M_(m,n)(theta) = sup { sqrt(n/m) * s_theta(A) : every row of A has norm 1 }`.

Let `a_theta` and `h_theta` be the Gaussian quantile and truncated second
moment from IE-21, and set `c_theta = sqrt(h_theta)`.

The full intended conclusion has both equivalent asymptotic forms:

1. For every `epsilon > 0`, there are integers `N,R` such that for all
   `n >= N` and all `m` with `m/n >= R`, every unit-row `A` satisfies
   `sqrt(n/m) * s_theta(A) <= c_theta + epsilon`.
2. No smaller constant has this eventual uniform upper-bound property, and
   along every regime `n -> infinity`, `m/n -> infinity`,
   `M_(m,n)(theta) -> c_theta`.

The paper records the uniform upper statement as
`sqrt(n/m) s_theta(A) <= c_theta + o_(n->infinity)(1)` uniformly in `m` and
unit-row `A`; the epsilon/N/R form is the definition to formalize.

## Quantitative universal-bound claims

The proof chooses an integer `1 <= r < n`, puts `d=n-r`, projects away the
leading `r` covariance eigendirections, and obtains
`||B||_2^2 <= m/(r+1)`, `||b_i|| <= 1`, and `tr(B^T B) <= m`. With
`L=2/(1-theta)`, a threshold-grid spacing `delta` gives exceptional
probability
`2/(r+1) + 4*L*(L/delta+2)/((r+1)*delta^2)
 + 2/((n-r)*delta^2)` and the bound
`(n/m)*s_theta(A)^2 <= n/((n-r)*(1-delta)) * (h_theta+2*delta)`.
The proof's variance estimates are `Var(Psi_t) <= 4*t/(r+1)` and
`Var(m^(-1)||B*g||^2) <= 2/(r+1)`. The asymptotic choice is
`r=floor(n^(2/3))`, `delta=n^(-1/6)`, giving a uniform loss
`O_theta(n^(-1/6))`. These constants and the quantifier order are retained;
the target is not reduced to a fixed finite-dimensional inequality.

## Constants and domains

`theta` is fixed in `(0,1)`; `m,n` are positive integers; row norms are exactly
one; subsets have cardinality `floor(theta*m)`; the supremum is over all real
unit-row matrices, with no random-matrix assumption. The Gaussian constant is
the same `h_theta` and `c_theta` as IE-21.

## Formalization boundary for approval

Prove the complete eventual-uniform upper bound, the optimality/no-smaller-
constant assertion, and the supremum convergence. A proof of only the random
row construction belongs to IE-21 and is insufficient for IE-22.
