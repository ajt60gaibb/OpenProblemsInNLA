# MD-06 statement specification

Source correspondence: `04_twenty_problem_resolutions/main.tex`, section
`sec:md`, theorem `md-main`; canonical source snapshot
`sources/aa8d010bdd5a/matrix-discrepancy-and-optimization/MD-06/README.md`.

## Complete probabilistic target

For every even integer `n >= 4`, let `G_n` be uniform on labelled simple
3-regular graphs with vertex set `{1,...,n}`. On the torus
`T^n = (R/(2*pi Z))^n`, define

`E_G(theta) = sum_{ {u,v} in E(G) } (1 - cos(theta_u-theta_v))`.

A phase is synchronized exactly when all coordinates agree modulo `2*pi`.
Local minima are with respect to the torus topology and need not be strict.
The intended negative resolution is

`lim_{n -> infinity, n even} P(every local minimum of E_(G_n) is synchronized) = 0`.

More strongly, with probability tending to one there is a nonsynchronized
critical point `theta_*` such that every edge cosine is greater than `1/32`
(the paper theorem states the displayed lower-bound form) and, for every
`z` in the mean-zero subspace `one^perp`,

`z^T * Hessian(E_(G_n))(theta_*) * z >= (1/320) * ||z||_2^2`.

## Supporting constants and domains

The correction lemma assumes a connected finite graph with at least two
vertices, Laplacian gap `lambda_gap >= gamma > 0`, a lift `phi`, edge cosines
at least `c > 0`, and
`||gradient E_G(phi)|| < c^2*gamma/(4*sqrt(2))`. It returns
`h_* in one^perp` with `||h_*|| < c/(2*sqrt(2))`, an exact local minimum
`phi+h_*`, edge cosines at least `c/2`, and Hessian lower bound
`(c*gamma/2) I` on `one^perp`.

For the cycle/tree construction, `ell` is a positive multiple of four,
`R >= 4`, `gamma=1/10`, `c_0=sqrt(1-t_4^2) > 1/16`,
`F_R(t)=3 asin(t)+2 sum_{j=1}^{R-1} asin(t/2^j)`, and `t_R` is the unique
root `F_R(t_R)=2*pi` in `(0,1)`. The profile is
`delta_j=asin(t_R/2^j)`, `a_j=sum_{s=j}^{R-1} delta_s`, `a_R=0`, with
`2*a_0+delta_0=2*pi`, `sin(2*a_0)=-t_R`, and
`cos(2*a_0)=sqrt(1-t_R^2) >= c_0`.

A clean radius-`R` neighbourhood of an `ell`-cycle in a connected cubic graph
with Laplacian gap at least `gamma` suffices when
`2^(R-1) > 32*ell/(c_0^4*gamma^2)`. The paper gives the explicit choice
`R=29+ceil(log_2 ell)` for `gamma=1/10`, and uses cycle Poisson mean
`mu_ell=2^ell/(2*ell)`, spectral-gap probability tending to one, and
nonclean-neighbourhood probability `O_(ell,R)(n^-1)`. These numerical claims
and the order of limits (first fixed `ell,R`, then `n`, then `ell`) are part of
the intended proof record.
