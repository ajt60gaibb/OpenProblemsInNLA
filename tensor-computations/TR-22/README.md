# TR-22 — Discreteness from below of asymptotic tensor rank

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** Open  
**Last checked:** 2026-09-10

**Rating rationale:** Finiteness would impose a general structural restriction on computational costs defined through arbitrarily large tensor powers, beyond known one-sided discreteness. This foundational constraint matters to the tensor-complexity community.

## Problem statement

For a complex tensor $T\in V_1\otimes\cdots\otimes V_k$, let $R(T)$ be the smallest number of decomposable tensors whose sum is $T$, with $R(0)=0$. The Kronecker power $T^{\boxtimes m}$ groups corresponding factors and lies in $V_1^{\otimes m}\otimes\cdots\otimes V_k^{\otimes m}$. Define
$$
\widetilde R(T)=\lim_{m\to\infty}R(T^{\boxtimes m})^{1/m}.
$$
For every fixed order $k\geq3$ and fixed positive dimensions $d_1,\ldots,d_k$, is
$$
\{\widetilde R(T):T\in\mathbb C^{d_1}\otimes\cdots\otimes\mathbb C^{d_k}\}
$$
a finite set?

Equivalently, in each fixed format, must every convergent sequence of attainable asymptotic ranks eventually be constant? The equivalence uses the already established closedness and discreteness from above. This asks for discreteness from below as posed in §5 of the source, in its explicitly discussed fixed-format form. There is no requirement that the finitely many values be integers, or that an algorithm compute them.

## Why it matters

Asymptotic rank controls the exponential cost of repeated multilinear computations. Finiteness would constrain how many distinct asymptotic computational costs can occur within one finite tensor space. It is weaker than the corresponding full asymptotic-rank conjecture and is different from the catalog's conjecture restricted to tight tensors.

## References and status check

1. M. Christandl, K. Hoeberechts, H. Nieuwboer, P. Vrana, and J. Zuiddam, *Asymptotic tensor rank is characterized by polynomials*, [arXiv:2411.15789v2](https://arxiv.org/pdf/2411.15789v2), §5 first bullet, p.17; Corollary 4.8 supplies the fixed-format formulation.
2. The same authors, [STOC 2025 paper](https://ir.cwi.nl/pub/36100/36100.pdf), pp.750–755, especially p.753, discussion of discreteness from below.
3. J. Zuiddam, [November 2025 research slides](https://staff.fnwi.uva.nl/j.zuiddam/talks/simons-14nov-2025.pdf), slide headed “Open problems,” repeats the question.

### Status check — 2026-09-10

Checked the June 2026 arXiv revision, §5 first bullet and Corollary 4.8, the STOC 2025 discussion, and targeted discreteness-from-below searches. These primary sources retain the fixed-format finiteness question. Discreteness results for finite coefficient sets do not establish it for arbitrary complex tensors, and established closedness and discreteness from above do not exclude accumulation from below. No full resolution was located in this bounded check. The separately posed irreducibility question would imply finiteness; no converse is asserted.
