# KE-01 — Exploit spectral outliers without losing input sparsity

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Topic:** sparse linear systems; randomized preconditioning  
**Last checked:** 2026-09-10  
**Status:** Open  

**Rating rationale:** Challenging reflects combining spectral deflation with an input-sparsity cost guarantee; community impact spans sparse solvers, preconditioning, and regression.

## Context and notation

All norms are Euclidean vector norms or their induced matrix norms.

## Problem statement

Let $A\in\mathbb R^{n\times n}$ be nonsingular, with singular values
$\sigma_1\geq\cdots\geq\sigma_n>0$, and write $N=\operatorname{nnz}(A)$
and $\kappa_2(A)=\sigma_1/\sigma_n$.
The input consists of its nonzero entries and their indices, $b\ne0$,
$\varepsilon\in(0,1/2)$, $k\in\{0,\ldots,n-1\}$, and $\kappa\geq1$, with the promise
$\sigma_{k+1}/\sigma_n\leq\kappa$. Fix any exponent $\omega_0>2$ for which
square matrix multiplication has an $O(m^{\omega_0})$ arithmetic algorithm.

Does a randomized algorithm exist that, for every such input, produces
$\widehat x$ satisfying

$$
\|A\widehat x-b\|_2\leq\varepsilon\|b\|_2
$$

with probability at least $0.99$, using at most

$$
C\bigl(k^{\omega_0}+N\kappa\bigr)
\bigl[1+\log(n\kappa_2(A)/\varepsilon)\bigr]^q
$$

exact arithmetic operations? Here $C,q$ may depend on the chosen multiplication
algorithm, but not on the input. Direct entry access is allowed. The display
makes the workshop's suppressed logarithms and accuracy convention explicit;
$\omega_0$ avoids assuming that the infimum defining the multiplication
exponent is attained.

## References

Amsel et al., [*Linear Systems and Eigenvalue Problems*](https://arxiv.org/html/2602.05394v3#S2.SS4),
Definition 2.4 and Problem 2.5. Dereziński and Sidford,
[*Approaching Optimality for Solving Dense Linear Systems with Low-Rank Structure*](https://doi.org/10.1137/1.9781611978971.37),
SODA 2026, pp. 925–938; [full manuscript](https://arxiv.org/html/2507.11724),
Theorems 3 and 29, gives the dense-input predecessor.

## Earlier status check — 2026-09-08

Searches for `sparse outlying singular values solver 2026`
and `spectral outliers linear systems 2026` found the newer Liu, Nguyen, Peng,
and Yang [*Faster Solvers for Sparse Systems with Large Spectral Outliers*](https://yangpliu.github.io/pdf/faster-solvers-sparse-spectral-outliers.pdf).
Its Theorem 1.1 assumes an explicitly given factor $B$ in $B^TBx=b$, bounded
spectral tail, polynomial conditioning, and short rational input. For an
$m\times d$ factor with at most $s$ nonzeros per row, its bit bound includes
$m^{o(1)}\widetilde O(ms+\sqrt{d/k}\,k^2+k^{\omega+\eta})$. These input
restrictions and extra terms do not establish the requested general bound.
The workshop's August update records this as partial progress on Problem 2.9.

## Audit update — 2026-09-10

Rechecked [workshop Problem 2.5](https://arxiv.org/html/2602.05394v3) and [Liu–Nguyen–Peng–Yang](https://yangpliu.github.io/pdf/faster-solvers-sparse-spectral-outliers.pdf), Theorem 1.1. The latter is a meaningful newer sparse-factor result but retains different input assumptions and overhead, as detailed above. Spectral-outlier solver searches found no theorem establishing this entry's exact general bound; the author-hosted manuscript is identifiable through [Liu's publication list](https://yangpliu.github.io/research.html).
