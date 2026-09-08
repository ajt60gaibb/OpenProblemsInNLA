# MF-04 — Finiteness for nonnegative rational matrix families

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** open; explicitly retained in a 2025 follow-up  
**Last checked:** 2026-09-08  

## Context and notation

The joint spectral radius of a nonempty compact set $\mathcal M\subset\mathbb C^{d\times d}$ is

$$
\widehat\rho(\mathcal M)=\lim_{k\to\infty}
\max_{A_1,\ldots,A_k\in\mathcal M}\|A_k\cdots A_1\|_2^{1/k}.
$$

This definition also applies to finite real matrix sets. The ordinary spectral
radius of one matrix is written $\rho(A)$.

## Problem statement

Does every finite nonempty set
$\mathcal M\subset\mathbb Q_{\ge0}^{d\times d}$, for every positive integer
$d$, admit a positive integer $k$ and matrices
$A_1,\ldots,A_k\in\mathcal M$ such that

$$
\widehat\rho(\mathcal M)=\rho(A_k\cdots A_1)^{1/k}?
$$

The entries must be nonnegative rationals; unrestricted real entries change the
status. This asks whether a finite product realizes the asymptotic growth rate.

## References and status evidence

Jungers and Blondel,
[On the finiteness property for rational matrices](https://arxiv.org/abs/math/0702489),
Linear Algebra Appl. 428 (2008), 2283–2295,
[DOI](https://doi.org/10.1016/j.laa.2007.07.007), abstract and reduction theorems;
Jungers, *The Joint Spectral Radius: Theory and Applications*,
[Chapter 4](https://doi.org/10.1007/978-3-540-95980-9_5), pp. 63–74 (2009).
They reduce this question to pairs of binary matrices in arbitrary dimension.
Mejstrik,
[The finiteness conjecture for 3×3 binary matrices](https://arxiv.org/pdf/2505.10178),
§3 and Theorem 3.1 (2025 preprint), treats the all-dimensions problem as open
while proving the binary-pair case in dimension three. Searches for rational
finiteness and binary-pair counterexamples through the check date found no
resolution of the general question. Equivalent binary formulations count once.
