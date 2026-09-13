# IS-03 — Johnson's derivative-realizability conjecture

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Solved  
**Last checked:** 2026-09-11  

**Rating rationale:** Challenging reflects preserving nonnegative realizability under polynomial differentiation; community impact connects the nonnegative inverse eigenvalue problem with polynomial critical points.

## Resolution — 2026-09-11

**Negative resolution by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. [Complete manuscript](solution.md) · [PDF](solution.pdf) · [LaTeX](solution.tex). **Theorem 1 and equations (1)–(7).**

The nonnegative real order-seven matrix $`A=\mathop{\mathrm{diag}}\nolimits(1/2,C_2,C_4)`$ has a normalized characteristic-polynomial derivative whose seventh power sum is $`-8593/823543<0`$. Every power of a nonnegative matrix has nonnegative trace, so the derivative cannot be realized at order six, or after any zero padding. Reducibility and positive trace are allowed in the original target. This refutes its universal assertion.

The complete argument received an independent Codex-agent **PASS** on 11 September 2026. The [review report](../../references/colbrook-additional-2026-09-11/verification/reviews/IS-03-review.md) records the exact scope and a hash of the original reviewed manuscript. The mathematical sections remain unchanged in the authored version. Original ChatGPT generation is disclosed; no external human peer review or formal proof certificate is asserted. [Submission and verification record](../../references/colbrook-additional-2026-09-11/README.md).

The original statement, source references and prior audit notes are retained; the former difficulty rating is historical.

## Problem statement

For every integer $`n\geq5`$ and every real entrywise-nonnegative matrix
$`A\in\mathbb R^{n\times n}`$, define $`p_A(z)=\det(zI-A)`$.
Must there exist an entrywise-nonnegative
$`B\in\mathbb R^{(n-1)\times(n-1)}`$ such that

```math
\det(zI-B)=\frac1n p_A'(z)\qquad\text{as polynomials in }z?
```

Equivalently, the critical points of the characteristic polynomial, counted
with multiplicity, would themselves form a realizable spectrum of the smaller
order. Neither $`A`$ nor $`B`$ is assumed symmetric or diagonalizable. The
realization must have exactly order $`n-1`$; allowing arbitrary additional zero
eigenvalues changes the problem. This would provide a dimension-reduction
operation for nonnegative spectral realization.

## References

Hoover, McCormick, Paparella, and Thrall,
[*On the realizability of the critical points of a realizable list*](https://arxiv.org/pdf/1712.05454),
Conjecture 1.2, p. 2, and §6. The paper credits the conjecture to Johnson and
records the Cronin–Laffey low-order results.

## Earlier status check — 2026-09-08

Searches for `Johnson conjecture derivative nonnegative
matrix characteristic polynomial proof counterexample`, `1712.05454 2026`,
and `Monov conjecture solved` found no general resolution. The source proves
several classes and records the solved cases $`n\leq4`$, and
$`n\leq6`$ with $`\mathop{\mathrm{tr}}\nolimits A=0`$. Nonnegative power sums alone are a
different hypothesis. Monov's weaker moment conjecture is not separately
counted here.

## Audit update — 2026-09-10

Rechecked the [primary manuscript](https://arxiv.org/pdf/1712.05454), Conjecture 1.2 and its proved families; the [journal version](https://doi.org/10.1016/j.laa.2018.06.024) is LAA 555 (2018), 301–313. Results for Ciarlet/Suleĭmanova lists, appropriate companion-matrix realizations, and trace-zero lists of orders five and six settle substantive portions of the displayed target. Johnson-conjecture/critical-point searches found no general proof or counterexample.
