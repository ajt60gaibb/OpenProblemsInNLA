# IE-21 statement specification

Source correspondence: `04_twenty_problem_resolutions/main.tex`, section
`sec:rows`, theorem `thm:row-random`; canonical source snapshot
`sources/aa8d010bdd5a/linear-systems-and-elimination/IE-21/README.md`.

## Canonical target

Fix a real parameter `theta` with `0 < theta < 1`. For positive integers `m,n`
and `A : R^(m x n)`, let `k = floor(theta*m)` and

`s_theta(A) = min_{S subset {1,...,m}, |S|=k} sigma_min(A_S)`,

where `A_S` retains exactly the rows in `S`, and `sigma_min` is the variational
minimum over unit vectors (so it is zero for a nontrivial kernel). Equivalently,
`s_theta(A)^2` is the minimum over unit `x` of the sum of the `k` smallest
values among `|(A*x)_i|^2`. Empty sums are zero.

Let `G` be standard normal, let `a_theta > 0` be the unique value with
`P(|G| <= a_theta) = theta`, and define

`h_theta = E[G^2 * 1_{|G| <= a_theta}]`
`       = (1/sqrt(2*pi)) * integral_{-a_theta}^{a_theta} t^2 exp(-t^2/2) dt`.

For every sequence of positive integer pairs `(m_j,n_j)` with
`n_j -> infinity` and `m_j/n_j -> infinity`, let `A_j` have independent rows
uniform on the sphere `S^(n_j-1)`. The primary conclusion is

`s_theta(A_j)^2 / ||A_j||_2^2 -> h_theta` in probability.

The collected paper also states the stronger pair of component conclusions

`(n_j/m_j) * s_theta(A_j)^2 -> h_theta` in probability,
`(n_j/m_j) * ||A_j||_2^2 -> 1` in probability,

from which the ratio conclusion follows. These are retained in scope.

## Quantitative proof claims to preserve

The paper's fixed-direction and net proof uses `L = 2/(1-theta)`;
`0 < epsilon <= (1-theta)/2`; `0 < t < 1`; `0 < delta < 1`; a covariance
failure bound `2*9^n*exp(-m*t^2/512)`; a trimming failure bound
`5*(1+2/delta)^n*exp(-2*m*epsilon^2)`; and error
`D = 2*L*epsilon + L/m + 2*(1+t)*delta`, followed by the Gaussian comparison
error `sqrt(2/n)`. The convergence choice is
`Q=m/n` and `t=epsilon=delta=32*sqrt(log(Q)/Q)` for sufficiently large `Q`.
The remaining displayed numerical inputs to that argument are: for
`Y^(n)=n*u_1^2`, `E[(Y^(n))^r] <= 2^r*r!`,
`E[|Y^(n)-1|^r] <= 4^r*r!`, and the centered MGF bound
`E[exp(lambda*(Y^(n)-1))] <= exp(32*lambda^2)` for `|lambda| <= 1/8`;
the resulting covariance tail is `2*9^n*exp(-m*t^2/512)`. The fixed-direction
trimmed-mean bound is
`P(|T_m-h_(theta,n)| > 2*L*epsilon + L/m)
 <= 5*exp(-2*m*epsilon^2)` under the stated epsilon restriction. The final
rate is `O_theta(sqrt((n/m)*log(m/n)) + n^(-1/2) + m^(-1))`.
The exact formal target must not silently remove the sequence quantifiers,
the floor convention, the sphere distribution, or the ratio normalization.

## Formalization boundary for approval

Formalize the complete probabilistic/asymptotic theorem above, including the
definitions and the two component limits, rather than only a finite numerical
example or a fixed direction. Supporting lemmas may expose the trimmed-moment,
net, covariance and Gaussian-coupling claims separately.
