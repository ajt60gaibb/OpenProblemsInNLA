# AC-08 — Knuth–Stolarsky lower bound for addition chains

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to specialist  
**Rating rationale:** Extreme because this universal binary-weight lower bound is a longstanding barrier in optimal addition-chain analysis; specialist importance is its role in proving and pruning minimum-multiplication powering algorithms.  
**Topic:** lower bounds for multiplication-only powering  
**Last checked:** 2026-09-10  
**Status:** Partially resolved  

## Context and notation

An addition chain for a positive integer $`n`$ is a sequence
$`1=a_0<a_1<\cdots<a_r=n`$ in which every $`a_i`$ with $`i>0`$ is a sum of two earlier
terms, which may coincide. Let $`\ell(n)`$ be its minimum possible length $`r`$.

The case $`n=1`$ uses $`\ell(1)=0`$.

## Problem statement

Let $`\nu(n)`$ be the number of
ones in the binary expansion of a positive integer $`n`$. Is

```math
\ell(n)\ge \lfloor\log_2 n\rfloor+
 \lceil\log_2\nu(n)\rceil\qquad(n\ge1)?
```

These rounding conventions are part of the statement. This would constrain
multiplication chains for $`A^n`$ and complements the upper bound in [AC-07](../AC-07/README.md).

## References and status

E. G. Thurber,
[*The Scholz–Brauer problem on addition chains*](https://msp.org/pjm/1973/49-1/pjm-v49-n1-p25-s.pdf),
Pacific Journal of Mathematics 49 (1973), p. 229, states the equivalent
small-step conjecture and treats a restricted case. H. Altman,
[*Internal structure of addition chains: Well-ordering*](https://www.sciencedirect.com/science/article/am/pii/S0304397517308666)
(2018), Conjecture 1.7 and §4, distinguishes proved cases from the general claim.
Searches for “Knuth Stolarsky conjecture 2026 proof” found no general resolution.
Bläser's Research Problem 2.10 is a discovery lead; this entry uses the explicit
floor/ceiling formulation in the specialized sources. **Admitted: no resolution
located.**

## Status check — 2026-09-10

Rechecked [Altman’s formulation and small-step results, thesis §4.4](https://hjaltman.github.io/thesis-FIXED.pdf), alongside the indexed 2018 journal text, and searched for later Knuth–Stolarsky resolutions. The conjecture is proved for small-step count at most three; the full inequality is not settled by those cases. No general proof or counterexample was located. The floor/ceiling convention is unchanged, and the later-status evidence is a bounded search without a new peer-reviewed general-status statement.
