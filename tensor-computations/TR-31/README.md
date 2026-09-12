# TR-31 — The four-exception conjecture for alternating tensor border-rank varieties

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to specialist  
**Status:** Partially resolved  
**Last checked:** 2026-09-10

**Rating rationale:** Excluding all additional defective Grassmannian secants is a longstanding classification barrier despite extensive proved parameter ranges. Its direct importance is to specialists in alternating tensor decompositions and secant geometry.

## Problem statement

For integers $`p\geq3`$ and $`N\geq2p`$, let

```math
C_{p,N}=\{v_1\wedge\cdots\wedge v_p:
v_1,\ldots,v_p\in\mathbb C^N\}\subset\bigwedge^p\mathbb C^N.
```

For every integer $`s\geq1`$, let
$`Y_s=\overline{\{x_1+\cdots+x_s:x_i\in C_{p,N}\}}^{\,\mathrm{Zar}}`$.
Its expected affine dimension is

```math
E_{p,N,s}=\min\left\{\binom Np,\ s\bigl(p(N-p)+1\bigr)\right\}.
```

Is $`\dim Y_s=E_{p,N,s}`$ except precisely for the following four triples, with the indicated actual affine dimensions?

```math
\begin{array}{c|r}
(p,N,s)&\dim Y_s\\\hline
(3,7,3)&34\\
(4,8,3)&50\\
(4,8,4)&64\\
(3,9,4)&74
\end{array}
```

Equivalently, the listed cases should exhaust the defective secant varieties of Grassmannians after using duality to impose $`N\geq2p`$. The restriction $`p\geq3`$ excludes the separate, already understood skew-symmetric matrix case. The dimension formula uses the affine cone, hence the $`+1`$ in each summand's parameter count.

## Why it matters

This predicts the dimensions of spaces of alternating tensors that admit a given number of decomposable wedge terms, including limiting decompositions. It gives the alternating-tensor analogue of generic rank formulas for symmetric tensors and identifies the exceptional formats where parameter counting mispredicts approximation complexity.

## References and status check

1. K. Baur, J. Draisma, and W. A. de Graaf, *Secant dimensions of minimal orbits: computations and conjectures*, [Experimental Mathematics **16** (2007), 239–250](https://doi.org/10.1080/10586458.2007.10128997), Conjecture 4.1; the original statement uses $`p>2`$ and $`2p\leq N`$.
2. A. Oneto and E. Ventura, *Ranks of tensors: geometry and applications*, [2025 survey](https://doi.org/10.1007/s40574-025-00472-9), §2.2.3, Conjecture 2.16; its projective notation has $`(k,n)=(p-1,N-1)`$.
3. A. Taveira Blomenhofer and A. Casarotti, *Nondefectivity of invariant secant varieties*, [Full preprint, v2](https://arxiv.org/html/2312.12335v2), §4, Theorem 4.3 and Remark 4.4.

### Status check — 2026-09-10

Checked the original-convention exception list against the 2025 restatement and Blomenhofer–Casarotti v2, Theorem 4.3 and Remark 4.4, with targeted later Grassmannian-defectivity searches. Theorem 4.3 proves nondefectivity for substantive general rank ranges, so Partially resolved applies to the displayed all-parameter target. These bounds leave intermediate ranks and do not exhaust the possible exceptions. The 2025 survey still states the four-exception conjecture; no full classification was located. The listed dimensions retain the affine-cone convention.
