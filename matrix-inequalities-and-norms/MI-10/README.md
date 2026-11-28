# MI-10 — Chollet's permanent inequality for Hadamard products

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** Solved  
**Last checked:** 2026-11-27

**Rating rationale:** The unrestricted PSD permanent inequality has resisted decades of work; it would advance a central collection of matrix-function inequalities.

## Resolution — 2026-11-27

**Solved affirmatively.** Zhouding Liu's
[*Gram variance and permutation information in Chollet's permanent
inequality*](https://doi.org/10.5281/zenodo.24423034), Theorem 1.1,
proves the inequality for complex Hermitian positive semidefinite
pairs of every order. Liu's matrix-to-scalar reduction combines
Gaussian moments, a matching law, and an entropy bound for a
permutation law. Yi Yu's
[independent proof of the scalar inequality](https://doi.org/10.5281/zenodo.24562562),
Theorem 3.1 and Remark 8.1, provides a second route to the required
nonnegative edge budgets.

The [independent informal Codex audit](solution.md) checked Liu's
reduction, verified the correspondence of the scalar budgets, and
regenerated and replayed all 360,174 boxes of Yu's nonnegativity
certificate with Arb interval arithmetic. Both manuscripts disclose
AI assistance.

For an $`n\times n`$ matrix $`C=(c_{ij})`$, define

```math
\mathop{\mathrm{per}}\nolimits C=\sum_{\sigma\in S_n}\prod_{i=1}^n c_{i,\sigma(i)}.
```

Is it true that, for every integer $`n\ge1`$ and every pair of complex Hermitian positive-semidefinite matrices $`A,B\in\mathbb C^{n\times n}`$,

```math
\mathop{\mathrm{per}}\nolimits(A\circ B)\le
(\mathop{\mathrm{per}}\nolimits A)(\mathop{\mathrm{per}}\nolimits B),
\qquad (A\circ B)_{ij}=a_{ij}b_{ij}?
```

## Relevance
 The Hadamard product preserves positive semidefiniteness and corresponds to tensor products of Gram vectors. The conjecture seeks a computable structural upper bound for a difficult matrix polynomial under this basic matrix operation. It concerns matrix inequalities and permanent computation.

## References

- J. Chollet, *Is there a permanental analogue to Oppenheim's inequality?*, American Mathematical Monthly 89 (1982), 57–58 ([original paper](https://doi.org/10.1080/00029890.1982.11995380)).
- P. Pant and R. Singh, *On Chollet's Permanent Conjecture for Graph Laplacians*, arXiv:2604.24192 (2026), abstract and introduction, with structured partial results ([primary manuscript](https://arxiv.org/abs/2604.24192)).
- Q. Li, Q. Zhao, and W. Luo, *Chollet's Permanent Conjecture Through Order Six via Border Induction*, posted 31 August 2026, Theorem 1.1 ([primary preprint](https://www.preprints.org/manuscript/202608.2196)).
- K. Rodtes, *Chollet’s permanent conjecture for $`4\times4`$ matrices*, Linear and Multilinear Algebra 72(16) (2024), 2633–2638. [Published paper](https://doi.org/10.1080/03081087.2023.2279150); [preprint](https://arxiv.org/abs/2211.02839).
- I. M. Wanless, *Lieb's permanental dominance conjecture* (2022), Conjecture 5 and the implication diagram distinguishing it from disproved stronger conjectures ([primary manuscript](https://arxiv.org/pdf/2202.01867)).

## Status check — 2026-09-10
 The August 2026 preprint claims the displayed inequality through order six. That claim has not been independently refereed here and does not claim the unrestricted result; the unresolved target includes orders $`n\ge7`$. The April 2026 paper addresses structured classes. Searches for “Chollet conjecture”, “permanent”, “proof”, and 2025–2026 found no general resolution. Disproofs of the stronger Bapat–Sunder and permanent-on-top conjectures do not refute this statement.

**Audit update (2026-09-10):** Rechecked the graph-Laplacian paper, the order-six preprint, and Rodtes’s order-four result, and searched for general resolutions. Added the published order-four reference to distinguish established low-order progress from the newer unrefereed order-six claim. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
