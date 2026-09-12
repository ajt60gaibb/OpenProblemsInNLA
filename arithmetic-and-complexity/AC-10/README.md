# AC-10 — An explicit rational Valiant-rigid matrix family

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Rating rationale:** Extreme because an explicit family at Valiant’s rank scale would break a longstanding linear-circuit lower-bound barrier; broad importance connects sparse perturbations, matrix structure and computational complexity.  
**Provenance:** rational-field specialization of a source-stated explicit-rigidity target.  
**Last checked:** 2026-09-10  

**Status:** Open  

For $`A\in\mathbb Q^{n\times n}`$ and an integer $`0\leq r\leq n`$, define its rigidity over $`\mathbb Q`$ by

```math
R_A^{\mathbb Q}(r)
=\min\left\{
|\{(i,j):A_{ij}\ne B_{ij}\}|:
B\in\mathbb Q^{n\times n},\
\mathop{\mathrm{rank}}\nolimits_{\mathbb Q}(B)\leq r
\right\}.
```

Construct a constant $`\delta>0`$ and a family $`A_n\in\mathbb Q^{n\times n}`$ such that a single deterministic algorithm, on input the unary encoding $`1^n`$, outputs all rational entries of $`A_n`$ in binary using polynomially many bit operations in $`n`$, and

```math
R_{A_n}^{\mathbb Q}
\left(\left\lfloor\frac{n}{\log\log n}\right\rfloor\right)
\geq n^{1+\delta}
```

for every sufficiently large integer $`n`$. Here $`\log`$ denotes the natural logarithm. The output convention requires polynomial total bit length; an exponentially long algebraic description does not meet this requirement.

Rigidity measures how resistant a matrix is to rank reduction by sparse entry changes. An explicit family at this scale would supply hard instances for linear circuit computation. The source states the target over a field; this entry explicitly selects rational entries and rational perturbations, rather than asserting that all choices of field are equivalent.

## References

1. J. Alman and J. Liang, *Low Rank Matrix Rigidity: Tight Lower Bounds and Hardness Amplification*, arXiv:2502.19580 (2025), Section 1 and Section 1.1: definition of rigidity, uniform polynomial-time explicitness, and the $`n/\log\log n`$ Valiant target. [Paper](https://arxiv.org/html/2502.19580v1).
2. L. Hambardzumyan, K. Myasnikov, A. Riazanov, M. Shirley, and A. Shraibman, *Spiky Rank and Its Applications to Rigidity and Circuits*, ICALP 2026, LIPIcs 374, article 106, Section 1.2.1: explicit rigidity remains insufficient for the relevant circuit lower bounds. [Published paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2026.106).
3. L. G. Valiant, *Graph-theoretic arguments in low-level complexity*, MFCS 1977, pp. 162–176, the original rigidity connection to linear circuits. [Article](https://doi.org/10.1007/3-540-08353-7_135).
4. Z. Dvir and A. Liu, *Fourier and Circulant Matrices are Not Rigid*, arXiv:1902.07334 (2019), main non-rigidity results for prominent structured candidates. [Paper](https://arxiv.org/abs/1902.07334).

## Status check — 2026-09-10

Rechecked [Alman–Liang, §1](https://arxiv.org/html/2502.19580v1) and the [ICALP 2026 spiky-rank paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2026.106), and searched for explicit rational Valiant-rigid constructions. The former’s low-rank bounds and conditional amplification do not meet the displayed n/log-log-n rank scale. No polynomial-time rational family meeting the target was located. The conclusion concerns rigidity over the rationals; results in other fields or for random matrices require a separate comparison.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
