# TR-25 — Cohen–Macaulay coordinate rings for every tensor border-rank variety

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to specialist  
**Status:** Partially resolved  
**Last checked:** 2026-09-10

**Rating rationale:** An all-format theorem would overcome longstanding obstructions in the local algebra of secant varieties and encompass other major Cohen–Macaulay conjectures. The depth and resolution questions chiefly concern specialists in tensor algebraic geometry.

## Problem statement

Fix integers $k\geq3$, $n_1,\ldots,n_k\geq1$, and $r\geq1$. In
$V=\mathbb C^{n_1}\otimes\cdots\otimes\mathbb C^{n_k}$, let
$$
X_r=\overline{\left\{
\sum_{\ell=1}^{r}v_{1,\ell}\otimes\cdots\otimes v_{k,\ell}:
v_{i,\ell}\in\mathbb C^{n_i}
\right\}}^{\,\mathrm{Zar}}.
$$
Let $S=\mathbb C[V]$ be the polynomial ring in the tensor entries, let $I(X_r)$ be its vanishing ideal, and let $A_r=S/I(X_r)$.

Is $A_r$ Cohen–Macaulay for every such format and rank threshold?

Explicitly, if $\mathfrak m$ is the ideal of positive-degree elements of $A_r$, the requested equality is
$$
\operatorname{depth}(A_r)_{\mathfrak m}
=\dim(A_r)_{\mathfrak m}.
$$
Depth is the maximum length of a regular sequence in the maximal ideal: each successive element is a non-zero-divisor after quotienting by its predecessors. Dimension is Krull dimension. This is Oeding's conjecture that all secant varieties of Segre products are arithmetically Cohen–Macaulay. The zero tensor is retained by using the affine cone.

## Why it matters

These are the algebraic sets underlying low-border-rank tensor approximation. Cohen–Macaulayness constrains their equations and free resolutions, supporting the determination of generators and the analysis of degeneracies. The conjecture does not assert that exact low-rank tensor approximation is computationally easy or always attained.

## References and status check

1. L. Oeding, *Are all Secant Varieties of Segre Products Arithmetically Cohen-Macaulay?*, [Preprint (2016), v2](https://arxiv.org/pdf/1603.08980v2), Conjecture 1.1, p.1; §2 collects established cases.
2. J. Jagiełła and J. Jelisiejew, *Unrestrictions and concise secant varieties*, [2026 preprint, v2](https://arxiv.org/html/2604.24879v2), Conjecture 3.32 and its surrounding discussion; §1.5.3 explains a connection to the Salmon ideal problem.

### Status check — 2026-09-10

Checked Oeding v2, including Theorems 3.1–3.2 and Proposition 3.5, and Jagiełła–Jelisiejew v2, Conjecture 3.32, with targeted later-resolution searches. Oeding proves substantive tensor cases, including the fourth secant of $\mathbb P^2\times\mathbb P^2\times\mathbb P^n$ for $n\ge3$, rather than only the matrix or rank-one cases. The June 2026 source still treats the all-format conjecture as open. Inheritance results require extra hypotheses and do not establish it universally. No full proof or counterexample was located.
