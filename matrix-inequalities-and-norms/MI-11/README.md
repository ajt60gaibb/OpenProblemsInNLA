# MI-11 — Lieb's permanental dominance conjecture

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-10-06

**Rating rationale:** This half-century-old dominance problem unifies many generalized matrix functions; its reach is substantial within matrix and representation theory.

Let $`n\ge1`$, let $`A=(a_{ij})\in\mathbb C^{n\times n}`$ be Hermitian positive semidefinite, let $`G`$ be any subgroup of the symmetric group $`S_n`$, and let $`\chi`$ be the character of any nonzero finite-dimensional complex representation of $`G`$. Thus $`\chi(e)>0`$, where $`e`$ is the identity. Define

```math
f_\chi(A)=\frac{1}{\chi(e)}
\sum_{\sigma\in G}\chi(\sigma)\prod_{i=1}^n a_{i,\sigma(i)},
\qquad
\mathop{\mathrm{per}}\nolimits A=\sum_{\sigma\in S_n}\prod_{i=1}^n a_{i,\sigma(i)}.
```

Does the inequality

```math
f_\chi(A)\le\mathop{\mathrm{per}}\nolimits A
```

hold for every such $`n,A,G,\chi`$? The character expression is real for Hermitian $`A`$, so the comparison is an ordinary real inequality.

## Relevance
 Generalized matrix functions include the determinant and immanants. The conjecture seeks a common upper bound across these structured matrix polynomials on the positive-semidefinite cone. It is part of matrix computation and matrix inequality theory, with links to symmetry reductions of tensor powers.

## References

- E. H. Lieb, *Proofs of some Conjectures on Permanents*, Journal of Mathematics and Mechanics 16 (1966), 127–134, Conjecture $`\alpha`$ on p.127 ([publisher's first page](https://iumj.s3-us-west-2.amazonaws.com/abstracts/16008_abs.pdf)).
- I. M. Wanless, *Lieb's permanental dominance conjecture* (2022), Conjecture 1, §2 implication diagram, and §3 partial results ([primary manuscript](https://arxiv.org/pdf/2202.01867)).
- A. Rico, D. Grinko, R. Krebs, and L. H. Zaw, *Entanglement Structure and Matrix Inequalities from Isotypic Measurements*, Physical Review Letters 137 (2026), 100203; abstract describes immanant inequalities for orders three and four ([journal](https://doi.org/10.1103/nvk2-h8d5)).
- Y. Li, *Lieb's Permanental Dominance Conjecture for Ordinary Immanants through Order Fifteen*, arXiv:2609.13412v1, submitted September 11, 2026. The primary abstract reports ordinary-immanant dominance through order fifteen and additional infinite families ([version 1 abstract](https://arxiv.org/abs/2609.13412v1)).

## Status check — 2026-09-10
 Searches for the exact conjecture name and “proof”, “counterexample”, and 2025–2026 found no general resolution. The September 2026 PRL abstract describes fixed-order progress. The August 2026 preprint *GPT, the Counterexample Machine*, §3.1, refutes a stronger conjecture for arbitrary real-stable polynomials; its example is not presented as a PSD-matrix counterexample to Lieb's conjecture ([primary manuscript](https://arxiv.org/html/2608.29595v1)). Likewise, the older disproof of permanent-on-top does not resolve the displayed statement.

**Audit update (2026-09-10):** Rechecked Wanless’s Conjecture 1 and implication diagram, and the 2026 counterexample paper’s discussion. Known immanant families are genuine subcases; the counterexample concerns a stronger real-stable-polynomial assertion, not the displayed PSD statement. This is a bounded literature check, not a proof that no solution exists.

## Literature update — 2026-10-06

Li's September 11 preprint reports that every normalized ordinary irreducible immanant is bounded by the permanent for every complex Hermitian positive-semidefinite matrix of order $`n\le15`$. Its abstract identifies the previously remaining partitions $`(4,4,3,3)`$, $`(5,4,3,3)`$, and $`(3^5)`$, and also reports infinite families including $`(m,4,3,3)`$ for $`m\ge4`$, $`(a,b,3,3)`$ for $`a\ge b\ge4`$ and $`5a\ge8b`$, and sufficiently long first rows with fixed tails. These are new ordinary-immanant subcases of the displayed conjecture ([primary abstract](https://arxiv.org/abs/2609.13412v1)).

**Scope and remaining gap:** The reported results concern irreducible characters of the full symmetric group in the stated orders and families. They do not supply a proof of the displayed statement for all orders, subgroups, and characters. The status remains **Partially resolved**. This update records the primary abstract's scope; no independent audit of the full proof or its finite and formal certificates was performed.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
