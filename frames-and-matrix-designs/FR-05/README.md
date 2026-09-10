# FR-05 — Vanishing injectivity probability at 4d minus 5 complex phase measurements

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Open  
**Last checked:** 2026-09-10

**Rating rationale:** The asymptotic typical-injectivity question needs quantitative algebraic and probabilistic control beyond positive failure probability; it informs phase-retrieval measurement design.


For every integer $d\geq2$, draw $A_d\in\mathbb C^{(4d-5)\times d}$ with independent standard complex Gaussian entries: the real and imaginary parts are independent $N(0,1/2)$. Let $p_d$ be the probability that
$$
|A_dx|=|A_dy|\quad\Longrightarrow\quad
y=e^{\mathrm i\theta}x\ \text{for some }\theta\in\mathbb R
$$
holds for all $x,y\in\mathbb C^d$, where absolute value is componentwise. Equivalently, $p_d$ is the probability that the induced phase-retrieval map on vectors modulo global phase is injective.

Is
$$
\lim_{d\to\infty}p_d=0?
$$

This is part (b) of Vinzant's conjecture as restated in Randomstrasse 101. It distinguishes injective exceptional measurement systems from typical matrices at a row count just below $4d-4$. Injectivity is the basic identifiability requirement before conditioning and stable numerical inversion can be addressed.

## References

1. A. S. Bandeira et al., *Randomstrasse 101: Open Problems of 2025*, arXiv:2603.29571 (2026), Conjecture 19(b). [Paper](https://arxiv.org/html/2603.29571v1).
2. C. Vinzant, *A small frame and a certificate of its injectivity*, SAMPTA 2015, arXiv:1502.04656. The explicit 11-vector frame in $\mathbb C^4$ demonstrates why the below-$4d-4$ regime cannot simply be dismissed. [Paper](https://arxiv.org/abs/1502.04656).
3. Z. Li, *On Injectivity of Phase Retrieval*, arXiv:2606.17922 (2026). The abstract and main result establish the strict inequality $p_d<1$, explicitly identifying this as the first part of Vinzant's conjecture. [Paper](https://arxiv.org/abs/2606.17922).

## Status check — 2026-09-10

Searched “Vinzant conjecture injectivity probability limit”, “phase retrieval 4M-5 2026”, and checked the latest June 2026 paper abstract/version. Its positive probability of noninjectivity does not supply an asymptotic lower bound tending to one. The already proved assertion $p_d<1$ is deliberately excluded from this problem.

**Audit update (2026-09-10):** Rechecked Li’s June 2026 abstract and searched for the asymptotic part of Vinzant’s conjecture. The reported strict inequality $p_d<1$ does not force $p_d\to0$; this entry contains only the latter target. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
