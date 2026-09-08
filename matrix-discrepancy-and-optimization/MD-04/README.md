# MD-04 — The Beck–Fiala discrepancy conjecture

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Provenance:** source-stated conjecture.  
**Last checked:** 2026-09-08

**Status:** no unrestricted resolution found in screening on 2026-09-08.  

Does a finite universal constant $C>0$ exist such that the following holds for every pair of positive integers $m,n$, every integer $t$ with $1\leq t\leq m$, and every matrix $A=(a_{ij})\in\{0,1\}^{m\times n}$?
If
$$
\sum_{i=1}^m a_{ij}\leq t\qquad(1\leq j\leq n),
$$
then some signing $x\in\{-1,1\}^n$ satisfies
$$
\|Ax\|_\infty\leq C\sqrt t.
$$
The constant must be independent of $m,n,t$. All columns are available when choosing the signing. The zero-sparsity case is trivial and excluded from the quantifiers.

The matrix is the incidence matrix of a set system: each element belongs to at most $t$ sets, and the signing should balance every set. The problem asks whether column sparsity alone controls the simultaneous row error at its conjectured square-root scale. It is a special case of the Komlós conjecture after column normalization, but an independent classical source-stated conjecture for incidence matrices.

## References

1. D. J. Altschuler and K. Tikhomirov, *Online Beck–Fiala Down to Logarithmic Sparsity*, arXiv:2607.14238 (2026), abstract and introduction: the unrestricted conjecture and the proved sparsity regime. [Paper](https://arxiv.org/html/2607.14238v1).
2. N. Bansal and H. Jiang, *Decoupling via Affine Spectral-Independence: Beck-Fiala and Komlós Bounds Beyond Banaszczyk*, arXiv:2508.03961v2 (2025), abstract and introductory results. [Paper](https://arxiv.org/abs/2508.03961).
3. J. Beck and T. Fiala, *“Integer-making” theorems*, Discrete Applied Mathematics 3(1) (1981), pp. 1–8, the original bounded-column-sparsity discrepancy results. [Article](https://doi.org/10.1016/0166-218X(81)90022-6).

## Status check — 2026-09-08

checked 2607.14238v1 (2026-07-15), 2508.03961v2 (2025-09-09), and searches “Beck Fiala conjecture solved 2026 logarithmic sparsity” and “Online Beck Fiala Down to Logarithmic Sparsity”. The 2026 work reaches sparsities $t\geq(\log n)^{1+o(1)}$ in its notation translated to $n$ columns; it does not establish the assertion for all sparsities. Online lower bounds concern a more restrictive information model. No full resolution or withdrawal was found.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
