# AC-06 — Explicit tensors with quadratic border rank

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Topic:** explicit lower bounds for tensor decompositions  
**Last checked:** 2026-09-08  
**Status:** open; admitted after a bounded literature search found no resolution.  

## Context and notation

Over $\mathbb C$, the tensor rank $R(T)$ is the minimum number of pure tensors in an exact sum for $T$. The border rank $\underline R_{\mathbb C}(T)$ is the least $r$ such that $T$ is a Euclidean limit of complex tensors of rank at most $r$.

## Problem statement

Construct a deterministic algorithm that, on input the positive
integer $n$, outputs the rational entries of a tensor
$T_n\in\mathbb Q^{n\times n\times n}$ in time polynomial in $n$, and prove that
there are constants $c>0,n_0$ such that
$\underline R_{\mathbb C}(T_n)\ge c n^2$ for all $n\ge n_0$.
Output rationals are encoded by binary integer numerators and denominators;
thus the time bound also limits their bit lengths. Border rank is over $\mathbb C$, as defined in the notation.

## Why it matters

Explicit hard tensors would supply lower bounds for
bilinear computation that are much stronger than the currently available
examples. Generic existence does not provide the required efficient construction.

## References and status

M. Michałek and J. Landsberg,
[*Towards Finding Hay in a Haystack: Explicit Tensors of Border Rank Greater
Than 2.02m*](https://www.theoryofcomputing.org/articles/v021a013/v021a013.pdf),
Theory of Computing 21(13), 2025, §1 and Definition 1.1, distinguishes
polynomial-time explicitness from weaker notions and obtains a linear bound.
The quadratic target and rational-output encoding are an editorial quantitative
formulation of the paper's explicit-versus-generic challenge, not a numbered
conjecture quoted from it. Searches for “explicit tensors
superlinear rank 2026” and “explicit tensors superlinear border rank” located
no quadratic construction; weaker semi-explicit constructions do not meet this
statement. **Admitted: no resolution located.**
