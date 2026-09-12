# MI-18 — Bapat's q-permanent monotonicity conjecture

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to specialist  
**Status:** Partially resolved  
**Last checked:** 2026-09-10

**Rating rationale:** Strict monotonicity on the whole PSD cone is a longstanding generalized-permanent barrier; its immediate impact is in specialist matrix-function inequalities.

## Problem statement

For a permutation $`\sigma\in S_n`$, let

```math
\mathop{\mathrm{inv}}\nolimits(\sigma)=
\#\{(i,j):1\le i< j\le n,\ \sigma(i)>\sigma(j)\}.
```

For real $`q`$ and $`A=(a_{ij})\in\mathbb C^{n\times n}`$, define

```math
P_q(A)=\sum_{\sigma\in S_n}q^{\mathop{\mathrm{inv}}\nolimits(\sigma)}
\prod_{i=1}^n a_{i,\sigma(i)},\qquad 0^0=1.
```

Is it true that, for every $`n\ge2`$, every non-diagonal Hermitian PSD matrix $`A`$ with $`a_{ii}>0`$ for all $`i`$, and every $`-1\le q_1< q_2\le1`$,

```math
P_{q_1}(A)< P_{q_2}(A)?
```

The expression is real for Hermitian $`A`$. The order of rows and columns in the inversion statistic is fixed.

## Relevance and ratings

 This polynomial interpolates $`\det A`$ at $`q=-1`$, the diagonal product at $`q=0`$, and $`\mathop{\mathrm{per}}\nolimits A`$ at $`q=1`$. The conjecture would compare a continuous family of matrix functions on the PSD cone, extending determinant/permanent inequalities. The non-diagonal and positive-diagonal hypotheses remove constant-polynomial cases.

## References

- R. B. Bapat and A. K. Lal, *Inequalities for the q-permanent*, Linear Algebra and its Applications 197–198 (1994), 397–409, monotonicity conjecture ([original paper](https://doi.org/10.1016/0024-3795(94)90497-9)).
- L. Mitchell, *A note on Bapat's q-permanent conjecture*, Operators and Matrices 14 (2020), 915–919, unnumbered Conjecture on p.917 and Theorems 1–3 ([primary paper](https://files.ele-math.com/articles/oam-14-56.pdf)).
- C. M. da Fonseca, *The $`\mu`$-permanent revisited* (2018), §4, related conjectures and corrections concerning ordered graph cases ([primary manuscript](https://arxiv.org/pdf/1804.02231)).

## Status check — 2026-09-10

 Mitchell proves that the original positive-definite conjecture is equivalent to the displayed extension, and proves rank-one and order-three cases. Searches for “Bapat q-permanent conjecture”, “monotonicity”, “proof”, “counterexample”, and 2025–2026 found no resolution. The stronger proposed extension beyond $`[-1,1]`$ is not included; Mitchell explains why extending that assertion to all PSD matrices fails. No recent explicit reaffirmation of the exact conjecture was found.

**Independent audit:** Independently rechecked Mitchell’s PSD-extension conjecture and rank-one theorem, and searched for later q-permanent monotonicity resolutions. Rank-one and low-order cases are substantive parts of the displayed family; the general case still has only historical-source status evidence.
