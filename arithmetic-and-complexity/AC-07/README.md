# AC-07 — Scholz–Brauer inequality for multiplication chains

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Topic:** multiplication counts for matrix powers  
**Last checked:** 2026-09-08  
**Status:** open; admitted after a bounded literature search found no resolution.  

## Problem statement

An addition chain for a positive integer $n$ is a sequence
$1=a_0<a_1<\cdots<a_r=n$ in which every $a_i$ with $i>0$ is a sum of two earlier
terms, which may coincide. Let $\ell(n)$ be its minimum possible length $r$.
Is

$$\ell(2^n-1)\le n+\ell(n)-1\qquad(n\ge1)?$$

The case $n=1$ uses $\ell(1)=0$. A chain implements a computation of $A^n$ by
matrix multiplications; the question is about this multiplication-only model,
not every possible matrix-function algorithm.

## References and status

Bläser, [2013](https://theoryofcomputing.org/articles/gs005/gs005.pdf),
Research Problem 2.9. N. Clift, [*A Short Note on Exact Equality for the
Scholz–Brauer Conjecture*](https://www.additionchains.com/ExactScholzBrauer.pdf)
(2024), distinguishes this inequality from the stronger equality and gives a
counterexample to equality. T. Agama,
[*A Progress on the Scholz Conjecture on Addition Chains*](https://www.researchgate.net/publication/397490267_A_PROGRESS_ON_THE_SCHOLZ_CONJECTURE_ON_ADDITION_CHAINS),
manuscript dated 10 May 2026, §1, still states the general inequality as open;
its result imposes additional conditions on an optimal addition chain.
Searches for “Scholz Brauer conjecture proof 2026” and inspection of these
sources found no proof or disproof of the unrestricted inequality.
**Admitted: no resolution located.**
