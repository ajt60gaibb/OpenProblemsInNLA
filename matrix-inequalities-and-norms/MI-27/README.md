# MI-27 — Constant one in the logarithmic commutator inequality

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** broadly interesting  
**Status:** Open  
**Last checked:** 2026-09-10

**Rating rationale:** Improving the known universal coefficient to its proposed sharp value is challenging; connections between matrix logarithms, entropy and quantum dynamics make the question broadly interesting.

## Problem statement

For every integer $`n\ge1`$ and positive definite $`A,B\in\mathbb C^{n\times n}`$ with $`\mathop{\mathrm{tr}}\nolimits(A+B)=1`$, set $`a=\mathop{\mathrm{tr}}\nolimits A`$, $`b=\mathop{\mathrm{tr}}\nolimits B`$. Is

```math
\bigl\|B\log(A+B)-\log(A+B)B\bigr\|_1
\le -a\log a-b\log b
```

always true? The logarithm is the natural logarithm applied by spectral functional calculus; $`\|X\|_1=\mathop{\mathrm{tr}}\nolimits(X^*X)^{1/2}`$. Thus $`a,b>0`$ and $`a+b=1`$, and every expression is well-defined.

The target is specifically the coefficient $`1`$ on the right. Existence of some dimension-independent coefficient has been proved and is not the open question. The coefficient-one question is explicitly suggested immediately after the original displayed conjecture.

This is a sharp matrix-function estimate for the rate at which noncommuting positive matrices mix. It connects perturbation estimates for the matrix logarithm with entropy production and quantum information.

## References

1. K. M. R. Audenaert and F. Kittaneh, *Problems and Conjectures in Matrix and Operator Inequalities*, arXiv:1201.5232v3 (2012), §6, Conjecture 4, equation (26), and the sentence proposing $`c=1`$. [Full text](https://arxiv.org/html/1201.5232).
2. K. M. R. Audenaert, *Quantum Skew Divergence*, J. Math. Phys. 55 (2014), 112202, §8, proof of small incremental mixing with coefficient $`2`$. [Full text](https://arxiv.org/html/1304.5935).
3. A. Vershynina, *Entanglement rates for Renyi, Tsallis and other entropies*, arXiv:1803.07117v3 (2021), §8, conclusion, pp. 15–16, explicitly distinguishing the proved coefficient $`2`$ and proposed coefficient $`1`$. [Full preprint](https://arxiv.org/pdf/1803.07117).

4. Q. Ning, F.-Z. Guo, J. Zhang and Q.-Y. Wen, *On Bounding Entangling Rates and Mixing Rates in Some Special Cases*, Int. J. Theor. Phys. 55 (2016), 1686–1694. [Published abstract](https://doi.org/10.1007/s10773-015-2806-9), which reports coefficient one under additional restrictions; the subscription body was not independently inspected in this audit.

Status check (2026-09-10): Audenaert's theorem settles the existence claim with $`2`$. Vershynina’s 2021 revision distinguishes the proved coefficient from the proposed coefficient $`1`$. Searches for “small incremental mixing sharp constant”, “logarithmic commutator Audenaert constant one”, and 2025/2026 found later special-case estimates but no announced universal coefficient-one proof or counterexample. This limited search does not certify that the conjecture remains open.
