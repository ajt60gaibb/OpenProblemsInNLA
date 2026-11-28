# TR-22 — Discreteness from below of asymptotic tensor rank

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** Open

**Last checked:** 2026-11-27

**Rating rationale:** Finiteness would impose a general structural restriction on computational costs defined through arbitrarily large tensor powers, beyond known one-sided discreteness. This foundational constraint matters to the tensor-complexity community.

## Problem statement

For a complex tensor $`T\in V_1\otimes\cdots\otimes V_k`$, let $`R(T)`$ be the smallest number of decomposable tensors whose sum is $`T`$, with $`R(0)=0`$. The Kronecker power $`T^{\boxtimes m}`$ groups corresponding factors and lies in $`V_1^{\otimes m}\otimes\cdots\otimes V_k^{\otimes m}`$. Define

```math
\widetilde R(T)=\lim_{m\to\infty}R(T^{\boxtimes m})^{1/m}.
```

For every fixed order $`k\geq3`$ and fixed positive dimensions $`d_1,\ldots,d_k`$, is

```math
\{\widetilde R(T):T\in\mathbb C^{d_1}\otimes\cdots\otimes\mathbb C^{d_k}\}
```

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

### Literature update — 2026-11-27

Liu's Corollary 3.4 determines the asymptotic rank of any three-tensor with
flattening ranks $`D,r_2,r_3`$ when $`D\ge2`$ and
$`r_2,r_3\le D^{\sqrt5/4}`$. The first flattening gives the lower bound $`D`$.
For the matching upper bound, the triangle in Theorem 3.1 has side lengths
$`1,\sqrt5/4,\sqrt5/4`$ in units of $`\log D`$. Its base midpoint gives the
rectangular matrix multiplication exponent $`\omega(1/4,1/2,1/2)=1`$.
[Liu, *A uniform exponent bound for asymptotic tensor rank*, Theorem 3.1 and Corollary 3.4](https://hexagonmath.org/pdf/2611.00972v1).

This yields the single value $`D`$ on the full first-flattening-rank locus
in every format $`D\times\lfloor D^t\rfloor\times\lfloor D^t\rfloor`$ for
fixed $`1/2< t\le\sqrt5/4`$ and sufficiently large $`D`$. In these formats the
generic border rank exceeds $`D`$ by the secant dimension bound. For example,
in format $`64\times10\times10`$, every tensor with first flattening rank
64 has asymptotic rank 64 and the generic border rank is at least 79.
Finiteness across all tensors of a fixed format still requires controlling
the other flattening-rank strata.

Vrana and Zuiddam prove that the spectral values of a *fixed* complex tensor
form the interval from its asymptotic subrank to its asymptotic rank. The
question here asks how many different upper endpoints occur as the tensor
varies within a fixed format. [Vrana–Zuiddam, *The asymptotic spectrum of tensors is connected*](https://arxiv.org/abs/2611.34664v1).
