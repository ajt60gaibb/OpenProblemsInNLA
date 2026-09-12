# AC-07 — Scholz–Brauer inequality for multiplication chains

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to specialist  
**Rating rationale:** Extreme because the unrestricted inequality is a longstanding frontier of addition-chain theory despite many proved structured cases; specialist importance reflects the multiplication-only powering model.  
**Topic:** multiplication counts for matrix powers  
**Last checked:** 2026-09-10  
**Status:** Partially resolved  

## Problem statement

An addition chain for a positive integer $`n`$ is a sequence
$`1=a_0<a_1<\cdots<a_r=n`$ in which every $`a_i`$ with $`i>0`$ is a sum of two earlier
terms, which may coincide. Let $`\ell(n)`$ be its minimum possible length $`r`$.
Is

```math
\ell(2^n-1)\le n+\ell(n)-1\qquad(n\ge1)?
```

The case $`n=1`$ uses $`\ell(1)=0`$. A chain implements a computation of $`A^n`$ by
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

## Status check — 2026-09-10

Added [Wallner, The Decompressed Tree Size of k-Ary Chains, §7](https://doi.org/10.1007/s00026-026-00816-y), published April 2026, which still identifies Scholz–Brauer as an open conjecture. Searches for full proofs found structured-chain and almost-all-integer claims, not the universal result; [Agama’s 2024 introduction](https://eprint.iacr.org/2024/1199.pdf) recalls Brauer’s proved star-optimal subclass. Clift’s counterexample concerns equality, not this upper bound. The [2016 “First Conjecture” paper](https://doi.org/10.4236/am.2016.71006) concerns elementary binary-length bounds, a different statement.
